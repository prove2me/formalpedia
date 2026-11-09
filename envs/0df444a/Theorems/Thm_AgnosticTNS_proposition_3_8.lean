-- Prove2me | Theorems.Thm_AgnosticTNS_proposition_3_8
-- name    : AgnosticTNS.proposition_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:39:18.062466+00:00
-- url     : https://prove2.me/theorems/68f17ce2-1948-4d48-94eb-fdd2c2866824
-- title:
--   Proposition 3.8 — tree tensor network representation of the output
-- statement:
--   Let $|\hat\psi\rangle$ be the output of Algorithm 1 on a run that completes all tomography calls, and write $s_i:=|R_i|=\min\{|M_i|,p_i\}$. Then $|\hat\psi\rangle$ is a tree tensor network on the dependency tree of $\mathcal L$, with the physical indices $F_i$ at node $i$. For every non-root node $i$, the bond joining $i$ to its parent has dimension at most
--   $$
--   d^{s_i}\le d^{p_i}\le d\left\lceil\frac{1024L^2r_i}{\min\{\epsilon,\vartheta\}^2}\right\rceil .
--   $$
--   The tensors can be constructed from the compression unitaries and the final residual vector in time polynomial in $L$ and $d^{a^{\mathrm{agn}}_{\max}}$.
--
--   In particular, for the rooted-subtree learning sequence of a tree $T=([n],E)$, the output is a TTN on $T$ with bond dimensions $O(dn^2\chi/\min\{\epsilon,\vartheta\}^2)$; and if the algorithm terminates early and returns $|0\rangle^{\otimes n}$, that state has a representation on the same tree with bond dimension one.
--
--   Differences from the source:
--   - encoding: vertices $[n]$, labels $[d]$, steps $[L]$ (1-based), vectors in $(\mathbb C^d)^{\otimes n}$ → `Fin n`, `Fin d`, `Fin L` (0-based), functions `(Fin n → Fin d) → ℂ`; reason: Lean convention; same instances
--   - encoding: standing assumptions $n\ge1$, $d\ge2$, $\epsilon\in(0,1]$, $\delta\in(0,1)$ of p.11 → explicit hypotheses; reason: the section's standing assumptions are binders
--   - encoding: Algorithm 1 (one execution, with its choices) → every admissible run (`Run.IsValid`) at the parameters $p_i,\Lambda_i$ of Section 3.2; reason: the algorithm makes choices ($R_i$, eigenvector spans, unitaries, top eigenvector); every choice is covered
--   - generalization: Sub-Tomography estimates are positive semidefinite of trace at most one → runs only need positive semidefinite estimates; reason: the class of runs is larger and contains every run of the paper's algorithm, so the statement specialises to the source's
--   - generalization: the bond of non-root node $i$ has dimension at most $d^{s_i}$ → the bond has dimension exactly $d^{s_i}$; reason: the proof gives equality ($\dim\mathcal H_{R_i}=d^{s_i}$), which implies the bound
--   - encoding: the tensors can be constructed in time polynomial in $L$ and $d^{a_{\max}}$ → one polynomial-time map sends the run's data (Gaussian-rational unitaries and residual vector, `encRunData`) padded with $L+d^{a_{\max}}$ ones to the description `encTTN` of the TTN; reason: running time on finite-precision data (Proposition 3.10); entries are exact Gaussian rationals
--   - reading: "the rooted-subtree learning sequence for a tree $T$" → every rooted-subtree learning sequence of $T$, for every root and every leaves-to-root order (`IsRootedSubtreeSeq`); reason: the page fixes neither the root nor the order; every choice is covered
--   - encoding: bond dimensions $O(dn^2\chi/\min\{\epsilon,\vartheta\}^2)$ (3.62) → bond at most $d\lceil1024n^2\chi/\min\{\epsilon,\vartheta\}^2\rceil$; reason: the explicit constant of (3.61) with $L=n$ and $r_i=\chi$, as in the proof on p.25
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Proposition 3.8, Eqs. (3.60)–(3.62), pp.24–25

import Mathlib
import Definitions.Def_AgnosticTNS_Run_IsValid
import Definitions.Def_AgnosticTNS_Run_psiHat
import Definitions.Def_AgnosticTNS_pP
import Definitions.Def_AgnosticTNS_LambdaP
import Definitions.Def_AgnosticTNS_aAgn
import Definitions.Def_AgnosticTNS_TTN_state
import Definitions.Def_AgnosticTNS_TTN_IsOn
import Definitions.Def_AgnosticTNS_encTTN
import Definitions.Def_AgnosticTNS_encRunData
import Definitions.Def_AgnosticTNS_IsRootedSubtreeSeq
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
open Matrix
open QAlgorithms.Complexity

namespace AgnosticTNS

/-- **Proposition 3.8 (Tree tensor network representation of the output)**, pp.24–25 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)). Let
`|ψ̂⟩` be the output of Algorithm 1 on a run that completes all tomography calls, and
`s_i := |R_i| = min{|M_i|, p_i}` (3.60). Then `|ψ̂⟩` is a tree tensor network on the dependency tree of
`L`, with the physical indices `F_i` at node `i`; for every non-root node `i`, the bond joining `i` to
its parent has dimension at most `d^{s_i} ≤ d^{p_i} ≤ d ⌈1024 L² r_i / min{ϵ, ϑ}²⌉` (3.61). The tensors
can be constructed from the compression unitaries and the final residual vector in time polynomial in
`L` and `d^{a^agn_max}`. In particular, for the rooted-subtree learning sequence of a tree
`T = ([n], E)` the output is a TTN on `T` with bond dimensions `O(d n² χ / min{ϵ, ϑ}²)` (3.62); and if the
algorithm terminates early and returns `|0⟩^{⊗n}`, that state has a representation on the same tree
with bond dimension one.

**Formalization Note** Runs are the valid runs of `Run.IsValid` at the §3.2 parameters. The bond of
non-root node `i` has dimension exactly `d^{s_i}`. "Time polynomial in `L` and `d^{a_max}`": one
polynomial-time map sends the run's data (`encRunData`, with Gaussian-rational unitaries and `φ̂`)
padded with `L + d^{a_max}` ones to the description `encTTN` of the TTN. The tree bound uses the
explicit constant of (3.61) with `L = n`, `r_i = χ`: `d ⌈1024 n² χ / min{ϵ, ϑ}²⌉`. -/
theorem proposition_3_8 :
    (∀ {n d : ℕ} (G : SimpleGraph (Fin n)) (χ : ℕ) (Ls : LearningSequence n) (ε ϑ : ℝ)
        (run : Run d n Ls),
      1 ≤ n → 2 ≤ d → 1 ≤ χ → 0 < ε → ε ≤ 1 → 0 < ϑ → ϑ ≤ 1 →
      run.IsValid (pP d G χ Ls ε ϑ) (LambdaP G χ Ls ε ϑ) →
      (∀ i, (run.R i).card = min (Mset Ls run.R i).card (pP d G χ Ls ε ϑ i)) ∧
      (∃ D : TTN Ls.L n d, (∀ v i, D.site v = i ↔ v ∈ Ls.F i) ∧
        (∀ i j, D.parent i = some j ↔ i ∈ Ls.I j) ∧
        (∀ i, i ≠ Ls.root → D.bond i = d ^ (run.R i).card) ∧
        D.state = run.psiHat (pP d G χ Ls ε ϑ)) ∧
      ∀ i, i ≠ Ls.root → d ^ (run.R i).card ≤ d ^ pP d G χ Ls ε ϑ i ∧
        d ^ pP d G χ Ls ε ϑ i ≤ d * ⌈1024 * (Ls.L : ℝ) ^ 2 * rr G χ Ls i / min ε ϑ ^ 2⌉₊) ∧
    (∃ f : Str → Str, PolyTimeComputable f ∧
      ∀ {n d : ℕ} (G : SimpleGraph (Fin n)) (χ : ℕ) (Ls : LearningSequence n) (ε ϑ : ℝ)
        (run : Run d n Ls),
        1 ≤ n → 2 ≤ d → 1 ≤ χ → 0 < ε → ε ≤ 1 → 0 < ϑ → ϑ ≤ 1 →
        run.IsValid (pP d G χ Ls ε ϑ) (LambdaP G χ Ls ε ϑ) →
        (∀ i a b, ∃ q : ℚ × ℚ, run.U i a b = ⟨q.1, q.2⟩) →
        (∀ a, ∃ q : ℚ × ℚ, run.φhat a = ⟨q.1, q.2⟩) →
        ∃ D : TTN Ls.L n d, (∀ v i, D.site v = i ↔ v ∈ Ls.F i) ∧
          (∀ i j, D.parent i = some j ↔ i ∈ Ls.I j) ∧
          (∀ i, i ≠ Ls.root → D.bond i = d ^ (run.R i).card) ∧
          D.state = run.psiHat (pP d G χ Ls ε ϑ) ∧
          (∀ k a b c, ∃ q : ℚ × ℚ, D.tensor k a b c = ⟨q.1, q.2⟩) ∧
          f (encRunData run ++ unary (Ls.L + d ^ Finset.univ.sup (aAgn d G χ Ls ε ϑ))) =
            encTTN ⟨Ls.L, D⟩) ∧
    (∀ {n d : ℕ} (T : SimpleGraph (Fin n)) (χ : ℕ) (ℓ : Fin n) (Ls : LearningSequence n)
        (ε ϑ : ℝ) (run : Run d n Ls),
      1 ≤ n → 2 ≤ d → 1 ≤ χ → 0 < ε → ε ≤ 1 → 0 < ϑ → ϑ ≤ 1 → T.IsTree →
      IsRootedSubtreeSeq T ℓ Ls → run.IsValid (pP d T χ Ls ε ϑ) (LambdaP T χ Ls ε ϑ) →
      ∃ D : TTN n n d, D.IsOn T ∧
        (∀ v, D.parent v ≠ none → D.bond v ≤ d * ⌈1024 * (n : ℝ) ^ 2 * χ / min ε ϑ ^ 2⌉₊) ∧
        D.state = run.psiHat (pP d T χ Ls ε ϑ)) ∧
    ∀ {n d : ℕ} (T : SimpleGraph (Fin n)), 1 ≤ n → 2 ≤ d → T.IsTree →
      ∃ D : TTN n n d, D.IsOn T ∧ (∀ v, D.bond v = 1) ∧
        D.state = fun x => if ∀ v, (x v : ℕ) = 0 then 1 else 0 := by sorry

end AgnosticTNS
