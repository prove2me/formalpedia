-- Prove2me | Theorems.Thm_ContWeatherall_classification
-- name    : ContWeatherall.classification
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-18T19:40:28.9143+00:00
-- url     : https://prove2.me/theorems/70d102fd-7f37-4c59-a432-54c94907768e
-- title:
--   Continuum classification of the field-strength functor on a vector space
-- statement:
--   Throughout, $E$ is a real normed space, $F$ a real normed space (Banach where stated), forms are Mathlib's `E → E [⋀^Fin k]→L[ℝ] F`, $d$ is `extDeriv` ($d\omega(x)(v_0,\dots,v_k)=\sum_i(-1)^iD\omega(x)(v_i)(v_0,\dots,\widehat{v_i},\dots,v_k)$), smooth means `ContDiff ℝ ∞`, and $(K\omega)(x)(v)=\int_0^1t^k\,\omega(tx)(x,v)\,dt$ for a $(k+1)$-form $\omega$. `Pot P` has smooth 1-forms $A$ with $P(dA)$ as objects and smooth $\chi:E\to F$ with $A+d\chi=A'$ as arrows $A\to A'$; `Fld P` is discrete on smooth closed 2-forms satisfying $P$; `fieldStrength P` sends $A\mapsto dA$. If $F$ is complete and `Pot P` is nonempty: `fieldStrength P` is full and essentially surjective, and faithful iff $F$ is trivial; moreover $H^1=0$, $H^2=0$ on the $P$-sector, and $H^0=0$ iff $F$ is trivial.
-- source:
--   J. O. Weatherall, Understanding Gauge, Philos. Sci. 83 (2016) 1039-1049, https://arxiv.org/abs/1505.02229 (page numbers refer to arXiv v2), §3 p. 7 and §4 pp. 8-11 (Prop. 1, fn. 9, fn. 15; erratum to Prop. 2, p. 15); M. Spivak, Calculus on Manifolds (W. A. Benjamin, 1965), Theorem 4-11 (Poincaré lemma) and its proof

import Definitions.Def_ContWeatherall_defs

open CategoryTheory ContinuousAlternatingMap
open scoped ContDiff

namespace ContWeatherall

/-- Main goal: on a real normed space `E` with values in a real Banach space `F`, for any field
equation `P` admitting a potential, `A ↦ dA` is full and essentially surjective, and faithful iff
`F` is trivial; equivalently `H¹ = 0`, `H² = 0`, and `H⁰ = 0` iff `F` is trivial. -/
theorem classification {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (P : (E → E [⋀^Fin 2]→L[ℝ] F) → Prop) [Nonempty (Pot P)] :
    (fieldStrength P).Full ∧ (fieldStrength P).EssSurj ∧
      ((fieldStrength P).Faithful ↔ Subsingleton F) ∧
      H1Vanishes E F ∧ H2Vanishes P ∧ (H0Vanishes E F ↔ Subsingleton F) := by
  sorry

end ContWeatherall
