-- Prove2me | Theorems.Thm_ContWeatherall_gaugeHom_torsor
-- name    : ContWeatherall.gaugeHom_torsor
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-18T19:33:06.318182+00:00
-- url     : https://prove2.me/theorems/11731498-a44d-4ee7-ab42-5bfd5d369785
-- title:
--   Weatherall erratum: Hom(A, A') is an F-torsor
-- statement:
--   Throughout, $E$ is a real normed space, $F$ a real normed space (Banach where stated), forms are Mathlib's `E → E [⋀^Fin k]→L[ℝ] F`, $d$ is `extDeriv` ($d\omega(x)(v_0,\dots,v_k)=\sum_i(-1)^iD\omega(x)(v_i)(v_0,\dots,\widehat{v_i},\dots,v_k)$), smooth means `ContDiff ℝ ∞`, and $(K\omega)(x)(v)=\int_0^1t^k\,\omega(tx)(x,v)\,dt$ for a $(k+1)$-form $\omega$. `Pot P` has smooth 1-forms $A$ with $P(dA)$ as objects and smooth $\chi:E\to F$ with $A+d\chi=A'$ as arrows $A\to A'$; `Fld P` is discrete on smooth closed 2-forms satisfying $P$; `fieldStrength P` sends $A\mapsto dA$. For an arrow $f:A\to A'$: for every $c\in F$ there is an arrow $g:A\to A'$ with $\chi_g=\chi_f+c$, and every arrow $g:A\to A'$ satisfies $\chi_g=\chi_f+c$ for a unique $c\in F$.
-- source:
--   J. O. Weatherall, Understanding Gauge, Philos. Sci. 83 (2016) 1039-1049, https://arxiv.org/abs/1505.02229 (page numbers refer to arXiv v2), erratum to Proposition 2 (p. 15) and §4 fn. 15

import Definitions.Def_ContWeatherall_defs

open CategoryTheory ContinuousAlternatingMap
open scoped ContDiff

namespace ContWeatherall

/-- `Hom(A, A')` is an `F`-torsor: shifting a gauge arrow by a constant gives a gauge arrow, and
any two parallel gauge arrows differ by a unique constant. -/
theorem gaugeHom_torsor {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {P : (E → E [⋀^Fin 2]→L[ℝ] F) → Prop} {A A' : Pot P} (f : A ⟶ A') :
    (∀ c : F, ∃ g : A ⟶ A', g.chi = f.chi + fun _ => c) ∧
      ∀ g : A ⟶ A', ∃! c : F, g.chi = f.chi + fun _ => c := by
  sorry

end ContWeatherall
