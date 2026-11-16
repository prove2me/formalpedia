-- Prove2me | Theorems.Thm_AgnosticTNS_Supplement_theorem_1_2
-- name    : AgnosticTNS.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:43:07.256423+00:00
-- url     : https://prove2.me/theorems/e39e5fc4-7947-44ca-a6d6-5c7ef6ed0376
-- title:
--   Theorem 1.2 — agnostic learning from a contraction sequence with $\widetilde O(d^4n^{13}\chi^{6C}/\epsilon^{13})$ copies
-- statement:
--   Let $G$ be a connected graph on $n\ge2$ vertices and let a contraction sequence of $G$ of complexity (width) $C$ be given. Let $d\ge2$ and $\chi\ge1$. There is an agnostic learner that, for every $n$-qudit state $\rho$ (no promise on $\mathrm{OPT}_{G,\chi}(\rho)$), outputs with probability at least $1-\delta$ a classical description of a pure state $|\hat\psi\rangle$ with
--   $$
--   \langle\hat\psi|\rho|\hat\psi\rangle \ge \mathrm{OPT}_{G,\chi}(\rho)-\epsilon ,
--   $$
--   and:
--   1. it uses at most $C_0\big(d^4n^{13}\chi^{6C}/\epsilon^{13} + n^5\chi^{2C}\epsilon^{-5}\log(n/\delta)\big) = \widetilde O(d^4n^{13}\chi^{6C}/\epsilon^{13})$ copies, for an absolute constant $C_0$;
--   2. its running time is polynomial in $n$, $d$, $\chi^C$, $1/\epsilon$ and $\log(1/\delta)$;
--   3. the output is a tree tensor network on the binary contraction tree (the dependency tree of the reconstruction steps) whose residual bond dimensions are $O(dn^2\chi^C/\epsilon^2)$;
--   4. the output state can be prepared to any trace-norm accuracy $\zeta$ by a circuit with a number of gates polynomial in the same parameters and $\log(1/\zeta)$.
--
--   This extends agnostic tomography from trees to arbitrary connected graphs, with the contraction complexity in the exponent of $\chi$.
--
--   **Formalization Note** The informal Theorem 1.2 is stated at the precision of its formal version, Corollary 5.10 (p.44). Running time is a polynomial-time printer of the learner's Clifford+T circuit from the encoded instance padded in unary with $n+d+\chi^C+\lceil1/\epsilon\rceil+\lceil\log_2(1/\delta)\rceil$; the bond bound is $C_b\,dn^2\chi^C/\epsilon^2$ with an absolute $C_b$; the preparation circuit starts from $|0\cdots0\rangle$ and is required for every output string produced with positive probability.
--
--   Differences from the source:
--   - reading: informal theorem: copy complexity Õ(d⁴n¹³χ^{6C}/ε¹³) → explicit bound C₀(d⁴n¹³χ^{6C}/ε¹³ + n⁵χ^{2C}/ε⁵ · log(n/δ)); reason: Õ suppresses logarithmic factors including the dependence on 1/δ (p.3); this is the bound the proof of Corollary 5.10 gives from (5.21) at ϑ = ε with d^{p_C} ≤ 2048dn²χ^C/ε²
--   - reading: a tree tensor network on the tree formed by the dependencies between reconstruction steps → a TTN on the binary contraction tree (IsOnContractionTree) with every non-root bond ≤ C_b·d n² χ^C/ε², C_b absolute; n ≥ 2; reason: the precision of the formal version Corollary 5.10 (residual bond dimension O(dn²χ^C/ε²); Lemma 5.5 needs n ≥ 2)
--   - reading: the output state can also be prepared efficiently in the same parameters → for every output string produced with positive probability that decodes to a TTN with nonzero state and every ζ ∈ (0, 1), a Clifford+T circuit from |0…0⟩ with at most q(n + d + χ^C + ⌈1/ε⌉ + ⌈log₂(1/δ)⌉ + ⌈log₂(1/ζ)⌉) gates prepares it to trace norm ζ; reason: the shape of the base mission's Proposition 3.10 preparation clause (3.71)
--   - encoding: running time polynomial in n, d, χ^C, 1/ε, log(1/δ) → a polynomial-time printer of the learner's circuit from the encoded instance padded in unary with n + d + χ^C + ⌈1/ε⌉ + ⌈log₂(1/δ)⌉; reason: the base mission's model of running time
--   - encoding: an algorithm receiving copies, ε and δ → one learner family (a Clifford+T circuit on qubit encodings of the copies plus ancillas, measured at the end) indexed by the instance with ⌈1/ε⌉ and ⌈log₂(1/δ)⌉; reason: the base mission's learner model; real ε ∈ (0, 1], δ ∈ (0, 1) remain the guarantee's parameters
--   - encoding: a contraction sequence (contract non-loop edges until each component is one vertex) → a list of merged vertex-set pairs (IsContractionSeq) with complexity max |cut_G(A ∪ B)|; reason: Definition 5.4 and p.41: the degree of a created vertex is |cut_G(S)|
--   - encoding: output overlap ⟨ψ̂|ρ|ψ̂⟩ → overlap of the normalised decoded TTN state, expVal ρ ψ / ‖ψ‖²; reason: as in the base mission's Corollary 5.2
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Theorem 1.2, Eq. (1.3), p.3; formal version Corollary 5.10, Eq. (5.25), p.44 (with Corollary 5.9, Eqs. (5.21)–(5.22), p.43)

import Mathlib
import Definitions.Def_AgnosticTNS_CopyLearner_prob
import Definitions.Def_AgnosticTNS_CopyLearner_code
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
import Definitions.Def_AgnosticTNS_Supplement_encContrIndex
import Definitions.Def_AgnosticTNS_Supplement_IsContractionSeq
import Definitions.Def_AgnosticTNS_Supplement_contrComplexity
import Definitions.Def_AgnosticTNS_Supplement_IsOnContractionTree
import Definitions.Def_AgnosticTNS_decodeTTN
import Definitions.Def_AgnosticTNS_TTN_state
import Definitions.Def_AgnosticTNS_OPT
import Definitions.Def_AgnosticTNS_encOp
import Definitions.Def_AgnosticTNS_bitsSplit
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_traceNorm
open Matrix
open QAlgorithms.Complexity

namespace AgnosticTNS.Supplement

/-- **Theorem 1.2 (Agnostic learning from contractions, informal)**, p.3, at the precision of its
formal version Corollary 5.10, p.44 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)). Let `G` be a connected graph
with a given contraction sequence of width `C`. There is an agnostic learner satisfying (1.2) (output
`|ψ̂⟩` with `⟨ψ̂|ρ|ψ̂⟩ ≥ OPT_{G,χ}(ρ) − ϵ` with probability at least `1 − δ`) whose copy complexity and
running time are polynomial in `n, d, χ^C, 1/ϵ, log(1/δ)`. It uses `Õ(d⁴n¹³χ^{6C}/ϵ¹³)` copies (1.3). It
outputs a classical description of a TTN on the tree formed by the dependencies between reconstruction
steps (Corollary 5.10: with residual bond dimension `O(dn²χ^C/ϵ²)`). The output state can also be prepared
efficiently in the same parameters.

**Formalization Note** `n ≥ 2` (Lemma 5.5, Corollaries 5.9–5.10); `C` is the complexity of the given
sequence. One learner family on `(n, G, sequence, d, χ, ⌈1/ϵ⌉, ⌈log₂(1/δ)⌉)` for every state `ρ` (no promise
on `OPT`), one absolute constant `C₀`, one absolute bond constant `C_b`, one polynomial-time printer of the
circuit from the instance padded with `n + d + χ^C + ⌈1/ϵ⌉ + ⌈log₂(1/δ)⌉`, and one polynomial `q`. The `Õ`
is the explicit bound `C₀(d⁴n¹³χ^{6C}/ϵ¹³ + n⁵χ^{2C}/ϵ⁵ · log(n/δ))` given by (5.21) at `ϑ = ϵ` with
`d^{p_C} ≤ 2048dn²χ^C/ϵ²` (proof of Corollary 5.10). The output decodes (`decodeTTN`) to a TTN on the
binary contraction tree (`IsOnContractionTree`) with every non-root bond at most `C_b dn²χ^C/ϵ²` and
normalised overlap `≥ OPT_{G,χ}(ρ) − ϵ`. Preparation: for every output string produced with positive
probability on some state that decodes to a TTN with nonzero state, and every `ζ ∈ (0, 1)`, a Clifford+T
circuit from `|0…0⟩` with at most `q(n + d + χ^C + ⌈1/ϵ⌉ + ⌈log₂(1/δ)⌉ + ⌈log₂(1/ζ)⌉)` gates leaves the data
qubits within trace norm `ζ` of the encoded normalised output state. -/
theorem theorem_1_2 :
    ∃ (Lr : CopyLearner ContrIndex (fun i => i.n) (fun i => i.d)) (C₀ Cb : ℝ) (g : Str → Str)
      (q : Polynomial ℕ),
      0 < C₀ ∧ 0 < Cb ∧ PolyTimeComputable g ∧
      ∀ (n d χ : ℕ) (G : SimpleGraph (Fin n)) (steps : List (Finset (Fin n) × Finset (Fin n)))
        (ε δ : ℝ),
        2 ≤ n → G.Connected → IsContractionSeq G steps → 2 ≤ d → 1 ≤ χ →
        0 < ε → ε ≤ 1 → 0 < δ → δ < 1 →
        let Cs := contrComplexity G steps
        let i : ContrIndex := ⟨n, G, steps, d, χ, ⌈1 / ε⌉₊, ⌈Real.logb 2 (1 / δ)⌉₊⟩
        g (encContrIndex i ++ unary (n + d + χ ^ Cs + ⌈1 / ε⌉₊ + ⌈Real.logb 2 (1 / δ)⌉₊)) = Lr.code i ∧
          (Lr.copies i : ℝ) ≤ C₀ * ((d : ℝ) ^ 4 * (n : ℝ) ^ 13 * (χ : ℝ) ^ (6 * Cs) / ε ^ 13 +
            (n : ℝ) ^ 5 * (χ : ℝ) ^ (2 * Cs) / ε ^ 5 * Real.log (n / δ)) ∧
          (∀ ρ : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ, WildeQIT.IsDensityOperator ρ →
            1 - δ ≤ Lr.prob i ρ (fun s => ∃ D : TTN steps.length n d,
              decodeTTN n d s = some ⟨steps.length, D⟩ ∧ IsOnContractionTree steps D ∧
              (∀ j, D.parent j ≠ none →
                (D.bond j : ℝ) ≤ Cb * d * (n : ℝ) ^ 2 * (χ : ℝ) ^ Cs / ε ^ 2) ∧
              D.state ≠ 0 ∧ OPT d G χ ρ - ε ≤ expVal ρ D.state / ∑ x, ‖D.state x‖ ^ 2)) ∧
          ∀ s : Str, (∃ ρ : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ, WildeQIT.IsDensityOperator ρ ∧
              0 < Lr.prob i ρ (fun s' => s' = s)) →
            ∀ (m : ℕ) (D : TTN m n d), decodeTTN n d s = some ⟨m, D⟩ → D.state ≠ 0 →
            ∀ ζ : ℝ, 0 < ζ → ζ < 1 →
            ∃ (a : ℕ) (Cc : Layered (n * Nat.clog 2 d + a)),
              ((Cc.map List.length).sum : ℕ) ≤
                q.eval (n + d + χ ^ Cs + ⌈1 / ε⌉₊ + ⌈Real.logb 2 (1 / δ)⌉₊ + ⌈Real.logb 2 (1 / ζ)⌉₊) ∧
              WildeQIT.traceNorm ((Matrix.of fun X Y => ∑ b : Bits a,
                    runLayered Cc (fun z => if z = fun _ => false then 1 else 0)
                        ((bitsSplit _ _).symm (X, b)) *
                      star (runLayered Cc (fun z => if z = fun _ => false then 1 else 0)
                        ((bitsSplit _ _).symm (Y, b)))) -
                  encOp (((∑ x, ‖D.state x‖ ^ 2 : ℝ) : ℂ)⁻¹ • vecMulVec D.state (star D.state))) ≤ ζ := by sorry

end AgnosticTNS.Supplement
