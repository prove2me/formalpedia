-- Prove2me | Theorems.Thm_ErasureQTanner_theorem_7
-- name    : ErasureQTanner.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:07:13.258312+00:00
-- url     : https://prove2.me/theorems/f11ab594-5256-4d8d-af38-e5a2f9b360be
-- title:
--   Theorem 7 — tensoring preserves erasure decoding
-- statement:
--   Let $\rho_1,\rho_2\in[0,1]$, $\delta_1,\delta_2>0$, and let $C_1\subseteq\mathbb F_q^{n_1}$, $C_2\subseteq\mathbb F_q^{n_2}$ be linear codes with $\Pr_{x\sim\rho_i}[\mathrm{decode}(C_i,x)=0]\le\delta_i$. Then $C:=C_1\otimes C_2$ satisfies, for $\rho:=\rho_1+\rho_2-\rho_1\rho_2$,
--   $$\Pr_{x\sim\rho}[\mathrm{decode}(C,x)=0]\le\mathop{\mathbb E}_{x\sim\rho}[\dim S_C(x)]\le(\delta_1n_2+\delta_2)n_1n_2.$$
--   Combined with Lemma 13 it is what turns the capacity of random codes into the capacity of duals of tensor codes.
--
--   Differences from the source: none.
-- source:
--   H. D. Pfister, O. Sprumont, G. Zémor, Classical Tensor Codes and Quantum Tanner Codes Achieve Capacity on Erasure Channels, STOC 2027 submission (manuscript sha256 bf7a84a5…), Theorem 7, p.17

import Mathlib
import Definitions.Def_ErasureQTanner_noisyProb
import Definitions.Def_ErasureQTanner_covered
import Definitions.Def_ErasureQTanner_tensorF

set_option autoImplicit false

namespace ErasureQTanner

/-- **Theorem 7.** Pfister, Sprumont, Zémor, *Classical Tensor Codes and Quantum Tanner Codes Achieve Capacity on Erasure Channels*, STOC 2027 submission (manuscript sha256 bf7a84a5…), p.17: for `ρ₁, ρ₂ ∈ [0, 1]`, `δ₁, δ₂ > 0` and `q`-ary linear codes with
`Pr_{x∼ρ_i}[decode(C_i, x) = 0] ≤ δ_i`, the tensor code `C := C₁ ⊗ C₂` satisfies
`Pr_{x∼ρ}[decode(C, x) = 0] ≤ E_{x∼ρ}[dim S_C(x)] ≤ (δ₁n₂ + δ₂)n₁n₂` for `ρ := ρ₁ + ρ₂ − ρ₁ρ₂`. -/
theorem theorem_7 {F : Type*} [Field F] [Fintype F] {n₁ n₂ : ℕ} (ρ₁ ρ₂ δ₁ δ₂ : ℝ)
    (hρ₁ : ρ₁ ∈ Set.Icc (0 : ℝ) 1) (hρ₂ : ρ₂ ∈ Set.Icc (0 : ℝ) 1) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂)
    (C₁ : Submodule F (Fin n₁ → F)) (C₂ : Submodule F (Fin n₂ → F))
    (h₁ : noisyProb ρ₁ (decodeFails C₁) ≤ δ₁) (h₂ : noisyProb ρ₂ (decodeFails C₂) ≤ δ₂) :
    noisyProb (ρ₁ + ρ₂ - ρ₁ * ρ₂) (decodeFails (tensorF C₁ C₂)) ≤
        noisyExp (ρ₁ + ρ₂ - ρ₁ * ρ₂) (fun x => (Module.finrank F (covered (tensorF C₁ C₂) x) : ℝ)) ∧
      noisyExp (ρ₁ + ρ₂ - ρ₁ * ρ₂) (fun x => (Module.finrank F (covered (tensorF C₁ C₂) x) : ℝ)) ≤
        (δ₁ * n₂ + δ₂) * n₁ * n₂ := by sorry

end ErasureQTanner
