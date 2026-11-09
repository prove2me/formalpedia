-- Prove2me | Theorems.Thm_AgnosticTNS_corollary_5_1
-- name    : AgnosticTNS.corollary_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:42:33.590078+00:00
-- url     : https://prove2.me/theorems/975c47e9-9f89-4f15-abef-94aafbbd301c
-- title:
--   Corollary 5.1 — agnostic TTN tomography
-- statement:
--   Let $T$ be a tree on $n\ge2$ vertices with maximum degree $\Delta=\Delta(T)$, and $\rho$ an arbitrary $n$-qudit state with $\mathrm{OPT}_{T,\chi}(\rho)\ge\vartheta$. Then one can output $|\hat\psi\rangle$ with $\langle\hat\psi|\rho|\hat\psi\rangle\ge\mathrm{OPT}_{T,\chi}(\rho)-\epsilon$ with probability at least $1-\delta$, using
--   $$
--   O\!\left(\frac{n^5\chi^2}{\vartheta\min\{\epsilon,\vartheta\}^4}\Big(d^{2(1+bp_T)}+\log(n/\delta)\Big)\right)
--   $$
--   copies, where $b$ is the maximum number of children after rooting $T$ at a leaf and
--   $$
--   p_T:=\max\left\{1,\left\lceil\log_d\frac{2048n^2\chi}{\min\{\epsilon,\vartheta\}^2}\right\rceil\right\}.
--   $$
--   For $n\ge3$, $b\le\Delta-1$. For fixed $\Delta$, both the number of copies and the running time are polynomial in $n,d,\chi,1/\epsilon,1/\vartheta,\log(1/\delta)$. The output has a TTN representation on $T$ with bond dimension at most $d^{p_T}$.
--
--   Differences from the source:
--   - encoding: vertices $[n]$, labels $[d]$, steps $[L]$ (1-based), vectors in $(\mathbb C^d)^{\otimes n}$ → `Fin n`, `Fin d`, `Fin L` (0-based), functions `(Fin n → Fin d) → ℂ`; reason: Lean convention; same instances
--   - encoding: standing assumptions $n\ge1$, $d\ge2$, $\epsilon\in(0,1]$, $\delta\in(0,1)$ of p.11 → explicit hypotheses; reason: the section's standing assumptions are binders
--   - encoding: an algorithm using copies, with gate count and classical time bounds → one learner family: a Clifford+T circuit on $\lceil\log_2 d\rceil$-qubit encodings of the copies plus ancillas, measured at the end, whose description is printed by a polynomial-time map; reason: house model of uniform quantum algorithms; the paper's learner measures copies jointly and adaptively, which a circuit with deferred measurements realises
--   - encoding: real $\epsilon,\vartheta$ and $\delta$ → $\epsilon,\vartheta$ exact rationals in the instance, $\delta$ entering as $\lceil\log_2(1/\delta)\rceil$ with the guarantee stated for the real $\delta$; reason: an algorithm's inputs are finite data; rounding $\epsilon,\vartheta$ would move the step functions $p_i$ and the factor $d^{2a_{\max}}$ by more than a constant
--   - encoding: a pure state $|\hat\psi\rangle$ given by a classical description → an output string that decodes (fixed decoder `decodeTTN`) to a TTN with Gaussian-rational entries; the overlap of its normalised state is used; reason: finite-precision output (Propositions 3.8, 3.10); the decoded vector need not be a unit vector, so it is normalised
--   - reading: $O(\cdot)$ copy bound → one absolute constant $C$ chosen before every instance; reason: the paper's constant in (3.54) is absolute
--   - reading: $b$, "the maximum number of children after rooting $T$ at a leaf" → `leafBranching T`, the least such maximum over the leaves; reason: the page does not name the leaf; the learner may choose it, and the minimum gives the larger class of trees for each $b$
--   - encoding: for fixed $\Delta$, copies and running time polynomial in $n,d,\chi,1/\epsilon,1/\vartheta,\log(1/\delta)$ → for every $\Delta$, a polynomial-time printer on the instance padded with $\lceil1/\epsilon\rceil+\lceil1/\vartheta\rceil$ ones and a polynomial bound on the copies, valid on all trees of maximum degree at most $\Delta$; reason: padding turns 'polynomial in $1/\epsilon,1/\vartheta$' into a running-time statement
--   - encoding: $\lceil\log_d X\rceil$ → `Nat.clog d ⌈X⌉₊`; reason: equal for $X\ge1$ and $d\ge2$
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Corollary 5.1, Eqs. (5.1)–(5.3), p.39

import Mathlib
import Definitions.Def_AgnosticTNS_CopyLearner_prob
import Definitions.Def_AgnosticTNS_CopyLearner_code
import Definitions.Def_AgnosticTNS_encTreeIndexQ
import Definitions.Def_AgnosticTNS_decodeTTN
import Definitions.Def_AgnosticTNS_TTN_state
import Definitions.Def_AgnosticTNS_TTN_IsOn
import Definitions.Def_AgnosticTNS_OPT
import Definitions.Def_AgnosticTNS_leafBranching
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
open Matrix
open QAlgorithms.Complexity
open Classical

namespace AgnosticTNS

/-- **Corollary 5.1 (Agnostic TTN tomography)**, p.39 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)). Let `T` be a tree on `n ≥ 2` vertices
with maximum degree `Δ = Δ(T)`, and `ρ` an arbitrary `n`-qudit state with `OPT_{T,χ}(ρ) ≥ ϑ`. Then one
can output `|ψ̂⟩` with `⟨ψ̂|ρ|ψ̂⟩ ≥ OPT_{T,χ}(ρ) − ϵ` (5.1) with probability at least `1 − δ`, using
`O(n⁵χ²/(ϑ min{ϵ, ϑ}⁴) · (d^{2(1 + b p_T)} + log(n/δ)))` copies (5.2), where `b` is the maximum number of
children after rooting `T` at a leaf and `p_T := max{1, ⌈log_d(2048 n² χ / min{ϵ, ϑ}²)⌉}` (5.3). For
`n ≥ 3`, `b ≤ Δ − 1`. For fixed `Δ`, both the number of copies and the running time are polynomial in
`n, d, χ, 1/ϵ, 1/ϑ, log(1/δ)`. The output has a TTN representation on `T` with bond dimension at most
`d^{p_T}`.

**Formalization Note** One learner family over `(n, T, d, χ, ϵ, ϑ, ⌈log₂(1/δ)⌉)` (`ϵ, ϑ` exact
rationals) with one absolute constant `C`; `b = leafBranching T` (some leaf). For every `Δ`, a
polynomial-time printer on the instance padded with `⌈1/ϵ⌉ + ⌈1/ϑ⌉` ones and a polynomial copy bound,
valid on the trees of maximum degree at most `Δ`. `⌈log_d X⌉ = Nat.clog d ⌈X⌉`. -/
theorem corollary_5_1 :
    ∃ (Lr : CopyLearner TreeIndexQ (fun i => i.n) (fun i => i.d)) (C : ℝ), 0 < C ∧
      (∀ (n d χ : ℕ) (T : SimpleGraph (Fin n)) (ε ϑ : ℚ) (δ : ℝ),
        2 ≤ n → T.IsTree → 2 ≤ d → 1 ≤ χ → 0 < ε → ε ≤ 1 → 0 < ϑ → ϑ ≤ 1 → 0 < δ → δ < 1 →
        (Lr.copies ⟨n, T, d, χ, ε, ϑ, ⌈Real.logb 2 (1 / δ)⌉₊⟩ : ℝ) ≤
            C * ((n : ℝ) ^ 5 * (χ : ℝ) ^ 2 / ((ϑ : ℝ) * (min (ε : ℝ) ϑ) ^ 4)) *
              ((d : ℝ) ^ (2 * (1 + leafBranching T *
                  max 1 (Nat.clog d ⌈2048 * (n : ℝ) ^ 2 * χ / (min (ε : ℝ) ϑ) ^ 2⌉₊))) +
                Real.log (n / δ)) ∧
          ∀ ρ : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ, WildeQIT.IsDensityOperator ρ →
            (ϑ : ℝ) ≤ OPT d T χ ρ →
            1 - δ ≤ Lr.prob ⟨n, T, d, χ, ε, ϑ, ⌈Real.logb 2 (1 / δ)⌉₊⟩ ρ
              (fun s => ∃ D : TTN n n d, decodeTTN n d s = some ⟨n, D⟩ ∧ D.IsOn T ∧
                (∀ v, D.parent v ≠ none → D.bond v ≤ d ^ max 1 (Nat.clog d ⌈2048 * (n : ℝ) ^ 2 * χ / (min (ε : ℝ) ϑ) ^ 2⌉₊)) ∧ D.state ≠ 0 ∧
                OPT d T χ ρ - ε ≤ expVal ρ D.state / ∑ x, ‖D.state x‖ ^ 2)) ∧
      (∀ (n : ℕ) (T : SimpleGraph (Fin n)), 3 ≤ n → T.IsTree → leafBranching T + 1 ≤ T.maxDegree) ∧
      ∀ Δ : ℕ, ∃ (g : Str → Str) (q : Polynomial ℕ), PolyTimeComputable g ∧
        ∀ (n d χ : ℕ) (T : SimpleGraph (Fin n)) (ε ϑ : ℚ) (δ : ℝ),
          2 ≤ n → T.IsTree → T.maxDegree ≤ Δ → 2 ≤ d → 1 ≤ χ → 0 < ε → ε ≤ 1 → 0 < ϑ → ϑ ≤ 1 →
          0 < δ → δ < 1 →
          g (encTreeIndexQ ⟨n, T, d, χ, ε, ϑ, ⌈Real.logb 2 (1 / δ)⌉₊⟩ ++
              unary (⌈1 / (ε : ℝ)⌉₊ + ⌈1 / (ϑ : ℝ)⌉₊)) =
            Lr.code ⟨n, T, d, χ, ε, ϑ, ⌈Real.logb 2 (1 / δ)⌉₊⟩ ∧
          Lr.copies ⟨n, T, d, χ, ε, ϑ, ⌈Real.logb 2 (1 / δ)⌉₊⟩ ≤
            q.eval (n + d + χ + ⌈1 / (ε : ℝ)⌉₊ + ⌈1 / (ϑ : ℝ)⌉₊ + ⌈Real.logb 2 (1 / δ)⌉₊) := by sorry

end AgnosticTNS
