-- Prove2me | Theorems.Thm_ArbLindbladLearn_fact_4_3
-- name    : ArbLindbladLearn.fact_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:24:58.634258+00:00
-- url     : https://prove2.me/theorems/ac845fba-37b7-4bc4-9b5b-c2ac66bb34ca
-- title:
--   Fact 4.3 — stabilizer states form an exact 3-design (moments)
-- statement:
--   Let $\varphi$ be a uniformly random element of $\mathrm{Stab}_n$ and $d=2^n$. Then
--   $$\mathbb E[\varphi]=\frac Id,\qquad\mathbb E[\varphi\otimes\varphi]=\frac{I\otimes I+\mathrm{SWAP}}{d(d+1)},\qquad\mathbb E[\varphi\otimes\varphi\otimes\varphi]=\frac{\sum_{\pi\in S_3}W_\pi}{d(d+1)(d+2)},$$
--   where SWAP exchanges the two factors and $W_\pi$ permutes the three factors according to $\pi$.
--
--   The second moment gives the unbiasedness of the process shadow (Lemma 4.4), the third its constant second moment (Lemma 4.5).
--
--   Differences from the source:
--   - encoding: E over a uniformly random φ ∈ Stab_n → |Stab_n|⁻¹ Σ_{φ ∈ Stab_n} via Set.ncard and finsum; reason: Stab_n is finite and nonempty; the average is the uniform expectation
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Fact 4.3, p.28 [KG15, Web16, Zhu17]

import Mathlib
import Definitions.Def_ArbLindbladLearn_Stab
import Definitions.Def_ArbLindbladLearn_permOp3

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker

namespace ArbLindbladLearn

open LindbladTolerant.Testing

/-- Fact 4.3 (Stabilizer moments [KG15, Web16, Zhu17]; Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.28). Let `φ`
be a uniformly random element of `Stab_n` and `d = 2ⁿ`. Then `E[φ] = I/d`,
`E[φ ⊗ φ] = (I ⊗ I + SWAP)/(d(d + 1))`, `E[φ ⊗ φ ⊗ φ] = Σ_{π ∈ S₃} W_π/(d(d + 1)(d + 2))`, where SWAP
exchanges the two factors and `W_π` permutes the three factors according to `π`.

**Formalization Note** `Stab_n = {C|0ⁿ⟩⟨0ⁿ|C† : C ∈ Cl_n}` (`Stab`); the uniform expectation is
`stabAvg` (finiteness of `Stab_n` is part of the content). `⊗` is the Kronecker product, so
`φ ⊗ φ ⊗ φ` acts on `(ℋ ⊗ ℋ) ⊗ ℋ`. Every `n`, including `n = 0`, is covered. -/
theorem fact_4_3 (n : ℕ) :
    stabAvg (fun φ : Op (Qubits n) => φ) = ((2 : ℂ) ^ n)⁻¹ • (1 : Op (Qubits n)) ∧
    stabAvg (fun φ : Op (Qubits n) => φ ⊗ₖ φ) =
      ((2 : ℂ) ^ n * ((2 : ℂ) ^ n + 1))⁻¹ • (1 + swapOp n) ∧
    stabAvg (fun φ : Op (Qubits n) => φ ⊗ₖ φ ⊗ₖ φ) =
      ((2 : ℂ) ^ n * ((2 : ℂ) ^ n + 1) * ((2 : ℂ) ^ n + 2))⁻¹ •
        ∑ π : Equiv.Perm (Fin 3), permOp3 n π := by sorry

end ArbLindbladLearn
