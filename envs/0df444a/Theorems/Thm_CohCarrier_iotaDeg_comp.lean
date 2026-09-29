-- Prove2me | Theorems.Thm_CohCarrier_iotaDeg_comp
-- name    : CohCarrier.iotaDeg_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/815b2f0e-fbb3-54d9-9037-831d1f209e20
-- title:
--   Composition of degeneracy maps ι_{d_1 d_2} = ι_{d_1}∘ι_{d_2}
-- statement:
--   Let $M_1,M_2,M_3$ and $d_1,d_2$ be natural numbers, with $M_2$, $M_3$, $d_1$, $d_2$ and $d_1d_2$ nonzero, and let $H_i$ be a subgroup of $(\mathbf{Z}/M_i)^\times$ for $i=1,2,3$. Assume three instances of the relation `LevelLE`, namely `LevelLE` for $(M_1,H_1)$ over $(M_2,H_2)$ at index $d_1$, for $(M_2,H_2)$ over $(M_3,H_3)$ at index $d_2$, and for $(M_1,H_1)$ over $(M_3,H_3)$ at index $d_1d_2$; each such relation asserts that the smaller modulus divides the larger, that the index divides the quotient of the moduli, and that the reduction map `ZMod.unitsMap` carries the larger group of units into the smaller one. Here `GammaH M H` is the subgroup of $\mathrm{SL}(2,\mathbf{Z})$ consisting of the matrices in $\Gamma_0(M)$ whose lower right entry reduces to an element of $H$, and `iotaDeg` sends such a matrix $\begin{pmatrix}a&b\\c&e\end{pmatrix}$ to $\begin{pmatrix}a&bd\\c/d&e\end{pmatrix}$, the conjugate by $\mathrm{diag}(d,1)$, which lies in the target group. The assertion is that for every $\gamma \in$ `GammaH M₃ H₃`, the value of `iotaDeg` at index $d_1d_2$ for the relation $h_{13}$ equals the value at index $d_2$ for $h_{23}$ followed by the value at index $d_1$ for $h_{12}$.
--
--   This is the compatibility of the degeneracy homomorphisms between the congruence subgroups $\Gamma_H(M)$ under composition: conjugating by $\mathrm{diag}(d_1d_2,1)$ is the same as conjugating successively by $\mathrm{diag}(d_2,1)$ and $\mathrm{diag}(d_1,1)$. It is used in the comparison of the images and indices of these maps, for instance in [`CohCarrier.index_range_iotaDeg_of_prime_sq`](thm.html#CohCarrier.index_range_iotaDeg_of_prime_sq) and [`CohCarrier.jDeg_iDeg_corner_of_prime_sq`](thm.html#CohCarrier.jDeg_iDeg_corner_of_prime_sq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_iotaDeg_comp.lean

import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.iotaDeg_comp {M₁ M₂ M₃ d₁ d₂ : ℕ} {H₁ : Subgroup (ZMod M₁)ˣ} {H₂ : Subgroup (ZMod M₂)ˣ}
    {H₃ : Subgroup (ZMod M₃)ˣ}
    [NeZero M₂] [NeZero M₃] [NeZero d₁] [NeZero d₂] [NeZero (d₁ * d₂)]
    (h₁₂ : LevelLE M₁ M₂ H₁ H₂ d₁) (h₂₃ : LevelLE M₂ M₃ H₂ H₃ d₂)
    (h₁₃ : LevelLE M₁ M₃ H₁ H₃ (d₁ * d₂)) (γ : ↥(GammaH M₃ H₃)) :
    iotaDeg M₁ M₃ H₁ H₃ (d₁ * d₂) h₁₃ γ
      = iotaDeg M₁ M₂ H₁ H₂ d₁ h₁₂ (iotaDeg M₂ M₃ H₂ H₃ d₂ h₂₃ γ) := by sorry
