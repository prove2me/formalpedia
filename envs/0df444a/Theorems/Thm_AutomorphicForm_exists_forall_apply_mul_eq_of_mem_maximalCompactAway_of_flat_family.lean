-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_apply_mul_eq_of_mem_maximalCompactAway_of_flat_family
-- name    : AutomorphicForm.exists_forall_apply_mul_eq_of_mem_maximalCompactAway_of_flat_family
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/061504d0-6e47-5d74-ab0f-f2ddf49602ee
-- title:
--   Uniform level for a flat family of induced sections
-- statement:
--   Let $F$ be a number field and let $\alpha : (\mathbb{A}_F)^\times \to \mathbb{R}^\times$ be the unit-group homomorphism obtained from the distributive Haar character of the adele ring $\mathbb{A}_F$ composed with the inclusion $\mathbb{R}_{\ge 0} \to \mathbb{R}$, and assume $\alpha(t) > 0$ for all $t$. Let $\varphi : \mathbb{C} \times \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$, written $\varphi_s(g)$, satisfy: (i) for each $s$, $\varphi_s$ is an induced section for the pair of characters $\mathrm{cpowChar}\,\alpha(s+1/2)$ and $\mathrm{cpowChar}\,\alpha(-(s+1/2))$, that is $\varphi_s(bg) = \chi_1(b_{11})\chi_2(b_{22})\varphi_s(g)$ for every $b$ in `adelicBorel` (upper triangular, $b_{21}=0$) and every $g$; (ii) for each $s$ and each infinite place $w$, the predicate `RightTranslatesSpanFinite` holds for $\varphi_s$ with respect to the row-isometry subgroup at $w$; (iii) for each $s$, $\varphi_s$ is a smooth vector for the right-translation action of the finite adelic subgroup; (iv) $(s,g)\mapsto \varphi_s(g)$ is continuous; (v) $s \mapsto \varphi_s(g)$ is differentiable for each $g$; (vi) flatness: $\varphi_s(k) = \varphi_{s'}(k)$ for all $s,s'$ whenever the finite part of $k$ lies in `finiteIntegralGL2` and every archimedean component of $k$ is a row isometry (unit determinant norm and preservation of the form $\|x\|^2+\|y\|^2$). Then there is a finite set $S_0$ of nonzero primes of $\mathcal{O}_F$ such that for all $s \in \mathbb{C}$, all $g$ and all $k$ lying in `maximalCompactAway F S₀` — i.e. $k$ integral and row-isometric as above, with trivial archimedean part and trivial component at each $v \in S_0$ — one has $\varphi_s(gk) = \varphi_s(g)$.
--
--   This is the statement that a flat, $K_f$-smooth family of Borel-induced sections on $\mathrm{GL}_2(\mathbb{A}_F)$ has a level independent of the spectral parameter: a single finite set of finite places outside which every member of the family is right invariant under the local integral subgroups. It is used in the analysis of the Weyl intertwining integral attached to such a family, where it allows the group variable to be controlled at finitely many places uniformly in $s$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_apply_mul_eq_of_mem_maximalCompactAway_of_flat_family.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.Analysis.Meromorphic.Order

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel Filter Topology
open scoped NNReal

theorem AutomorphicForm.exists_forall_apply_mul_eq_of_mem_maximalCompactAway_of_flat_family
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
      (_hφflat : ∀ (s s' : ℂ) (k : AdelicGL2 (𝓞 F) F),
          glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
          φ s k = φ s' k),
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)),
      ∀ (s : ℂ) (g k : AdelicGL2 (𝓞 F) F), k ∈ maximalCompactAway F S₀ → φ s (g * k) = φ s g := by sorry
