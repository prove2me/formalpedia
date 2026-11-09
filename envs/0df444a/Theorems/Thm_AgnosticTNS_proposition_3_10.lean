-- Prove2me | Theorems.Thm_AgnosticTNS_proposition_3_10
-- name    : AgnosticTNS.proposition_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:41:08.38924+00:00
-- url     : https://prove2.me/theorems/f038774e-7f5c-455d-b371-a985050ce0e8
-- title:
--   Proposition 3.10 — computational cost of the agnostic learner
-- statement:
--   Using the tomography procedure of Lemma 3.9 in Theorem 3.6, and writing $D=d^{a^{\mathrm{agn}}_{\max}}$ and $\Lambda_{\max}=\max_i\Lambda_i$, there is an implementation with the same asymptotic copy bound whose number of elementary quantum gates and classical bit complexity are polynomial in
--   $$
--   n,\ L,\ D,\ \Lambda_{\max},\ 1/\epsilon,\ 1/\vartheta,\ \log(1/\delta).
--   $$
--   The output description has length polynomial in these parameters. Given this description, a state within trace-norm error $\zeta$ of $|\hat\psi\rangle\langle\hat\psi|$ can be prepared with
--   $$
--   \mathrm{poly}\big(n,L,D,\log(1/\zeta),\log(1/\gamma_{\min}),\log(1/\epsilon)\big)
--   $$
--   elementary gates, where $\gamma_{\min}=\min_i\gamma_i$. The learning sequence is an input of the algorithm, and the learning stage runs over a fixed finite universal gate set with the same asymptotic bounds.
--
--   Differences from the source:
--   - encoding: vertices $[n]$, labels $[d]$, steps $[L]$ (1-based), vectors in $(\mathbb C^d)^{\otimes n}$ → `Fin n`, `Fin d`, `Fin L` (0-based), functions `(Fin n → Fin d) → ℂ`; reason: Lean convention; same instances
--   - encoding: standing assumptions $n\ge1$, $d\ge2$, $\epsilon\in(0,1]$, $\delta\in(0,1)$ of p.11 → explicit hypotheses; reason: the section's standing assumptions are binders
--   - encoding: an algorithm using copies, with gate count and classical time bounds → one learner family: a Clifford+T circuit on $\lceil\log_2 d\rceil$-qubit encodings of the copies plus ancillas, measured at the end, whose description is printed by a polynomial-time map; reason: house model of uniform quantum algorithms; the paper's learner measures copies jointly and adaptively, which a circuit with deferred measurements realises
--   - encoding: gates and classical time polynomial in $n,L,d^{a_{\max}},\max_i\Lambda_i,1/\epsilon,1/\vartheta,\log(1/\delta)$ → a polynomial-time printer of the circuit whose input is the instance padded with $n+L+d^{a_{\max}}+\Lambda_{\max}+\lceil1/\epsilon\rceil+\lceil1/\vartheta\rceil+\lceil\log_2(1/\delta)\rceil$ ones; reason: these quantities are not input lengths; padding makes 'polynomial in them' a running-time statement
--   - encoding: real $\epsilon,\vartheta$ and $\delta$ → $\epsilon,\vartheta$ exact rationals in the instance, $\delta$ entering as $\lceil\log_2(1/\delta)\rceil$ with the guarantee stated for the real $\delta$; reason: an algorithm's inputs are finite data; rounding $\epsilon,\vartheta$ would move the step functions $p_i$ and the factor $d^{2a_{\max}}$ by more than a constant
--   - encoding: a pure state $|\hat\psi\rangle$ given by a classical description → an output string that decodes (fixed decoder `decodeTTN`) to a TTN with Gaussian-rational entries; the overlap of its normalised state is used; reason: finite-precision output (Propositions 3.8, 3.10); the decoded vector need not be a unit vector, so it is normalised
--   - reading: $O(\cdot)$ copy bound → one absolute constant $C$ chosen before every instance; reason: the paper's constant in (3.54) is absolute
--   - encoding: the output description has polynomial length → the number of output wires is at most $q_0$ of the padding, for one polynomial $q_0$; reason: the description is the output string
--   - encoding: a state within $\zeta$ of $|\hat\psi\rangle\langle\hat\psi|$ can be prepared with $\mathrm{poly}(\cdot)$ elementary gates → for every output string produced with positive probability that decodes to a TTN with nonzero state $\psi$ and every $\zeta\in(0,1)$, a Clifford+T circuit started in $|0\cdots0\rangle$ with at most $q(n+L+D+\lceil\log_2(1/\zeta)\rceil+\lceil\log_2(1/\gamma_{\min})\rceil+\lceil\log_2(1/\epsilon)\rceil)$ gates whose data qubits, after tracing out its ancillas, are within trace norm $\zeta$ of the encoded $|\psi\rangle\langle\psi|/\|\psi\|^2$; reason: qubit encoding (3.68); one polynomial $q$ fixed before the instance
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Proposition 3.10, Eqs. (3.70)–(3.71), p.26

import Mathlib
import Definitions.Def_AgnosticTNS_CopyLearner_prob
import Definitions.Def_AgnosticTNS_CopyLearner_code
import Definitions.Def_AgnosticTNS_encSeqIndex
import Definitions.Def_AgnosticTNS_decodeTTN
import Definitions.Def_AgnosticTNS_TTN_state
import Definitions.Def_AgnosticTNS_OPT
import Definitions.Def_AgnosticTNS_aAgn
import Definitions.Def_AgnosticTNS_LambdaP
import Definitions.Def_AgnosticTNS_gammaP
import Definitions.Def_AgnosticTNS_LearningSequence_root
import Definitions.Def_AgnosticTNS_encOp
import Definitions.Def_AgnosticTNS_bitsSplit
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
open Matrix
open QAlgorithms.Complexity

namespace AgnosticTNS

/-- **Proposition 3.10 (Computational cost of the agnostic learner)**, p.26 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)). Using the
tomography procedure of Lemma 3.9 in Theorem 3.6, with `D = d^{a^agn_max}` and `Λ_max = max_i Λ_i`,
there is an implementation with the same asymptotic copy bound whose number of elementary quantum
gates and classical bit complexity are polynomial in `n, L, D, Λ_max, 1/ϵ, 1/ϑ, log(1/δ)` (3.70). The
output description has polynomial length in these parameters. Given this description, a state
within trace-norm error `ζ` of `|ψ̂⟩⟨ψ̂|` can be prepared using
`poly(n, L, D, log(1/ζ), log(1/γ_min), log(1/ϵ))` elementary gates (3.71), `γ_min = min_i γ_i`. The
learning sequence is an input. The learning stage can be implemented over a fixed finite universal
gate set with the same asymptotic bounds.

**Formalization Note** The learner, constant, printer and padding are those of `theorem_3_6`
(Clifford+T is a fixed finite universal gate set). The description length is the number of output
wires. For every output string that some input state produces with positive probability and that
decodes to a TTN with nonzero state `ψ`, and every `ζ ∈ (0, 1)`, a Clifford+T circuit on the
`n⌈log₂ d⌉` data qubits plus ancillas, started in `|0…0⟩`, with at most
`q(n + L + D + ⌈log₂(1/ζ)⌉ + ⌈log₂(1/γ_min)⌉ + ⌈log₂(1/ϵ)⌉)` gates (`q` fixed before the instance),
leaves the data qubits within trace norm `ζ` of the encoded `|ψ⟩⟨ψ|/‖ψ‖²`. -/
theorem proposition_3_10 :
    ∃ (Lr : CopyLearner SeqIndex (fun i => i.n) (fun i => i.d)) (C : ℝ) (g : Str → Str)
      (q₀ q : Polynomial ℕ),
      0 < C ∧ PolyTimeComputable g ∧
      ∀ (n d χ : ℕ) (G : SimpleGraph (Fin n)) (Ls : LearningSequence n) (ε ϑ : ℚ) (δ : ℝ),
        1 ≤ n → 2 ≤ d → 1 ≤ χ → 0 < ε → ε ≤ 1 → 0 < ϑ → ϑ ≤ 1 → 0 < δ → δ < 1 →
        g (encSeqIndex ⟨n, G, Ls, d, χ, ε, ϑ, ⌈Real.logb 2 (1 / δ)⌉₊⟩ ++
            unary (n + Ls.L + d ^ Finset.univ.sup (aAgn d G χ Ls ε ϑ) +
              Finset.univ.sup (LambdaP G χ Ls ε ϑ) + ⌈1 / (ε : ℝ)⌉₊ + ⌈1 / (ϑ : ℝ)⌉₊ +
              ⌈Real.logb 2 (1 / δ)⌉₊)) =
            Lr.code ⟨n, G, Ls, d, χ, ε, ϑ, ⌈Real.logb 2 (1 / δ)⌉₊⟩ ∧
          (Lr.copies ⟨n, G, Ls, d, χ, ε, ϑ, ⌈Real.logb 2 (1 / δ)⌉₊⟩ : ℝ) ≤
            C * ((Ls.L : ℝ) ^ 5 * ((Finset.univ.sup (rr G χ Ls) : ℕ) : ℝ) ^ 2 /
                ((ϑ : ℝ) * (min (ε : ℝ) ϑ) ^ 4)) *
              ((d : ℝ) ^ (2 * Finset.univ.sup (aAgn d G χ Ls ε ϑ)) + Real.log (Ls.L / δ)) ∧
          (Lr.out ⟨n, G, Ls, d, χ, ε, ϑ, ⌈Real.logb 2 (1 / δ)⌉₊⟩).length ≤
            q₀.eval (n + Ls.L + d ^ Finset.univ.sup (aAgn d G χ Ls ε ϑ) +
              Finset.univ.sup (LambdaP G χ Ls ε ϑ) + ⌈1 / (ε : ℝ)⌉₊ + ⌈1 / (ϑ : ℝ)⌉₊ +
              ⌈Real.logb 2 (1 / δ)⌉₊) ∧
          (∀ ρ : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ, WildeQIT.IsDensityOperator ρ →
            (ϑ : ℝ) ≤ OPT d G χ ρ →
            1 - δ ≤ Lr.prob ⟨n, G, Ls, d, χ, ε, ϑ, ⌈Real.logb 2 (1 / δ)⌉₊⟩ ρ
              (fun s => ∃ (m : ℕ) (D : TTN m n d), decodeTTN n d s = some ⟨m, D⟩ ∧
                D.state ≠ 0 ∧ OPT d G χ ρ - ε ≤ expVal ρ D.state / ∑ x, ‖D.state x‖ ^ 2)) ∧
          ∀ s : Str, (∃ ρ : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ, WildeQIT.IsDensityOperator ρ ∧
              0 < Lr.prob ⟨n, G, Ls, d, χ, ε, ϑ, ⌈Real.logb 2 (1 / δ)⌉₊⟩ ρ (fun s' => s' = s)) →
            ∀ (m : ℕ) (D : TTN m n d), decodeTTN n d s = some ⟨m, D⟩ → D.state ≠ 0 →
            ∀ ζ : ℝ, 0 < ζ → ζ < 1 →
            ∃ (a : ℕ) (Cc : Layered (n * Nat.clog 2 d + a)),
              ((Cc.map List.length).sum : ℕ) ≤
                q.eval (n + Ls.L + d ^ Finset.univ.sup (aAgn d G χ Ls ε ϑ) + ⌈Real.logb 2 (1 / ζ)⌉₊ +
                  ⌈Real.logb 2 (1 / Finset.univ.inf' ⟨Ls.root, Finset.mem_univ _⟩
                    (gammaP G χ Ls ε ϑ))⌉₊ + ⌈Real.logb 2 (1 / (ε : ℝ))⌉₊) ∧
              WildeQIT.traceNorm ((Matrix.of fun X Y => ∑ b : Bits a,
                    runLayered Cc (fun z => if z = fun _ => false then 1 else 0)
                        ((bitsSplit _ _).symm (X, b)) *
                      star (runLayered Cc (fun z => if z = fun _ => false then 1 else 0)
                        ((bitsSplit _ _).symm (Y, b)))) -
                  encOp (((∑ x, ‖D.state x‖ ^ 2 : ℝ) : ℂ)⁻¹ • vecMulVec D.state (star D.state))) ≤ ζ := by sorry

end AgnosticTNS
