-- Prove2me | Theorems.Thm_Algebra_exists_mem_comap_one_div_traceDual_mul_eq_mul_of_height_eq_one_of_charZero
-- name    : Algebra.exists_mem_comap_one_div_traceDual_mul_eq_mul_of_height_eq_one_of_charZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/b2b51d86-61b3-505f-b2d1-a2f5e9b72721
-- title:
--   Tame different bound at a height-one prime above t
-- statement:
--   Let $R$ be a Noetherian integrally closed commutative domain with fraction field $K$, let $S$ be an integrally closed commutative domain which is an $R$-algebra, finite and free as an $R$-module, and let $F$ be a field which is a fraction field of $S$ and carries $K$- and $R$-algebra structures compatible with those of $R \to K$, $R \to S$ (scalar towers $R \to K \to F$ and $R \to S \to F$), with $F$ separable over $K$; all four types lie in one universe. Let $t \in R$ be such that the ideal $(t)$ is prime and the residue ring $R/(t)$ has characteristic zero, and let $\mathfrak{Q} \subseteq S$ be a prime ideal of height $1$ with $t \in \mathfrak{Q}$ (that is, the image of $t$ under $R \to S$ lies in $\mathfrak{Q}$). The assertion is the existence of $s \in S$ lying in the different ideal of $S$ over $R$ — the preimage in $S$, along the $S$-linear map $S \to F$, of the submodule $1 / \mathfrak{C}$, where $\mathfrak{C} = \{x \in F : \operatorname{Tr}_{F/K}(x y) \in R \text{ for all } y \text{ in the image of } S\}$ is the trace dual of the unit $S$-submodule of $F$; this is Mathlib's `differentIdeal` with $K$ and $F$ in place of the fraction-ring constructions — together with $u \in S \setminus \mathfrak{Q}$ and $z \in \mathfrak{Q}$ satisfying $u\,t = s\,z$ in $S$.
--
--   This is the element-wise form of the tame different bound along the divisor $t = 0$: the relation $ut = sz$ with $u \notin \mathfrak{Q}$ and $z \in \mathfrak{Q}$ says that the order of the different at the height-one prime $\mathfrak{Q}$ is at most $v_{\mathfrak{Q}}(t) - 1$, as must happen when the residue characteristic is zero and the ramification is therefore tame. It feeds into [`Algebra.map_span_le_radical_mul_map_comap_one_div_traceDual_of_isUnramifiedAt_of_charZero`](thm.html#Algebra.map_span_le_radical_mul_map_comap_one_div_traceDual_of_isUnramifiedAt_of_charZero), and its proof invokes [`Ideal.ramificationIdx_pow_not_dvd_differentIdeal`](thm.html#Ideal.ramificationIdx_pow_not_dvd_differentIdeal).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_exists_mem_comap_one_div_traceDual_mul_eq_mul_of_height_eq_one_of_charZero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem Algebra.exists_mem_comap_one_div_traceDual_mul_eq_mul_of_height_eq_one_of_charZero
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Type u) [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [Algebra R S] [Module.Finite R S] [Module.Free R S]
    (F : Type u) [Field F] [Algebra S F] [IsFractionRing S F] [Algebra K F] [Algebra R F]
    [IsScalarTower R K F] [IsScalarTower R S F] [Algebra.IsSeparable K F]
    (t : R) (ht : (Ideal.span ({t} : Set R)).IsPrime) [CharZero (R ⧸ Ideal.span ({t} : Set R))]
    (𝔔 : Ideal S) [𝔔.IsPrime] (h𝔔 : 𝔔.height = 1) (ht𝔔 : algebraMap R S t ∈ 𝔔) :
    ∃ s ∈ ((1 / Submodule.traceDual R K (1 : Submodule S F) : Submodule S F).comap (Algebra.linearMap S F)), ∃ u ∉ 𝔔, ∃ z ∈ 𝔔, u * algebraMap R S t = s * z := by sorry
