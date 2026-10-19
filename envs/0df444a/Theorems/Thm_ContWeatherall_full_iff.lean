-- Prove2me | Theorems.Thm_ContWeatherall_full_iff
-- name    : ContWeatherall.full_iff
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-18T19:36:16.937022+00:00
-- url     : https://prove2.me/theorems/e1e9e721-1c80-45ba-b122-08ee677de063
-- title:
--   Weatherall §4 fn. 15 (continuum analogue): full iff H¹ = 0
-- statement:
--   Throughout, $E$ is a real normed space, $F$ a real normed space (Banach where stated), forms are Mathlib's `E → E [⋀^Fin k]→L[ℝ] F`, $d$ is `extDeriv` ($d\omega(x)(v_0,\dots,v_k)=\sum_i(-1)^iD\omega(x)(v_i)(v_0,\dots,\widehat{v_i},\dots,v_k)$), smooth means `ContDiff ℝ ∞`, and $(K\omega)(x)(v)=\int_0^1t^k\,\omega(tx)(x,v)\,dt$ for a $(k+1)$-form $\omega$. `Pot P` has smooth 1-forms $A$ with $P(dA)$ as objects and smooth $\chi:E\to F$ with $A+d\chi=A'$ as arrows $A\to A'$; `Fld P` is discrete on smooth closed 2-forms satisfying $P$; `fieldStrength P` sends $A\mapsto dA$. If `Pot P` is nonempty, `fieldStrength P` is full iff every smooth closed 1-form is $d\chi$ of a smooth $\chi$.
-- source:
--   J. O. Weatherall, Understanding Gauge, Philos. Sci. 83 (2016) 1039-1049, https://arxiv.org/abs/1505.02229 (page numbers refer to arXiv v2), §4 fn. 15 (EM2 with gauge arrows) and fn. 9; continuum twin of the discrete WeatherallGauge.full_iff

import Definitions.Def_ContWeatherall_defs

open CategoryTheory ContinuousAlternatingMap
open scoped ContDiff

namespace ContWeatherall

/-- If some potential exists, `A ↦ dA` is full iff `H¹ = 0`. -/
theorem full_iff {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (P : (E → E [⋀^Fin 2]→L[ℝ] F) → Prop) [Nonempty (Pot P)] :
    (fieldStrength P).Full ↔ H1Vanishes E F := by
  sorry

end ContWeatherall
