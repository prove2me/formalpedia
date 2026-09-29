-- Prove2me | Theorems.Thm_AutomorphicForm_exists_norm_a_le_absNorm_rpow_and_norm_b_le_of_smoothCuspRealizationAt_of_peterssonPairing
-- name    : AutomorphicForm.exists_norm_a_le_absNorm_rpow_and_norm_b_le_of_smoothCuspRealizationAt_of_peterssonPairing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/e851acb6-2326-57bc-bdd5-e33d06585092
-- title:
--   Polynomial bound on Hecke eigenvalues of a cusp realization
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2,s$ be real numbers, let $T$ be a finite set of elements of $\mathrm{GL}_2(\mathbb{A}_F)$, let $\pi'$ be a Hecke eigensystem over $\mathbb{C}$ for $F$ (a nonzero level ideal of $\mathcal{O}_F$ together with families $a_v,b_v\in\mathbb{C}$ indexed by the finite places), and let $S$ be a set of adelic matrices. Let $R'$ be a smooth cusp realization, on the carrier data `productionPinsOf` assembled from the domain $\bigcup_{x\in T}(\text{centre-cut Siegel set})\cdot x$ (the Siegel set being cut out by integrality of the finite component, lower bounds $c$ on the local heights, upper bounds $u^2$ on the window quantities and archimedean determinant norms in $[d_1,d_2]$), the level subgroups $N\mapsto\mathrm{levelOne}\cap\ker(\text{archimedean component})$, the standard Hecke generators `heckeGen` and the adelic box, of the rescaled eigensystem `π'.toRawCentral` (same level and same $a_v$, with $b_v$ replaced by $(\mathrm{N}v)^{-1}b_v$); thus $R'$ is a nowhere identically zero function on $\mathrm{GL}_2(\mathbb{A}_F)$ with a central character on the full centre subgroup, smooth and cuspidal in the sense of the carrier data, invariant under the level subgroup, and, outside a finite exceptional set of places, a Hecke coset eigenfunction at $v$ with eigenvalue $a_v$ and satisfying the central eigen-equation with eigenvalue $(\mathrm{N}v)^{-1}b_v$. Write $\langle x,y\rangle=\int_S x(g)\overline{y(g)}\,\|\det g\|_{\mathbb{A}_F}^{-s}\,dg$ for the Petersson integral with respect to adelic Haar measure, and let $V$ be the $\mathbb{C}$-span of the right translates $z\mapsto R'(zh)$. Assume: (i) $\langle x(\cdot\,g),y(\cdot\,g)\rangle=\|\det g\|_{\mathbb{A}_F}^{s}\langle x,y\rangle$ for all $g$ and all $x,y\in V$; (ii) $\langle R',R'\rangle\neq 0$; (iii) granting the tautological hypothesis that $R'$'s central character equals itself, the same covariance for $x\in V\sqcup V$, $y\in V$, together with a sesquilinear form $P$ (linear in the first variable, conjugate-linear in the second) enjoying the same covariance on those arguments, with $P(y,y)\neq 0$ for some $y\in V$, and agreeing with $\langle\cdot,\cdot\rangle$ there; and (iv) for every finite place $v$ the uniformizer idele has idele norm $(\mathrm{N}v)^{-1}$, where $\mathrm{N}v=\mathrm{absNorm}(v)$. Then there exists $\kappa\ge 0$ with $\|a_v\|\le(\mathrm{N}v)^{\kappa}$ and $\|b_v\|\le(\mathrm{N}v)^{\kappa}$ for every finite place $v$.
--
--   This is the polynomial growth of the Hecke eigenvalues and central eigenvalues of a cuspidal eigensystem, the hypothesis under which the associated Euler product converges absolutely in a right half-plane. It is used in the Rankin–Selberg part of the development, feeding the construction of test data for which the $s$-part integrals are analytic on a neighbourhood and nonvanishing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_norm_a_le_absNorm_rpow_and_norm_b_le_of_smoothCuspRealizationAt_of_peterssonPairing.lean

import Definitions.Def_AutomorphicForm_PeterssonIntegral
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_HeckeEigenfunction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField
open NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel
open IsDedekindDomain NumberField.TateGlobal

theorem AutomorphicForm.exists_norm_a_le_absNorm_rpow_and_norm_b_le_of_smoothCuspRealizationAt_of_peterssonPairing
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (π' : HeckeEigensystem F ℂ)
    (R' : SmoothCuspRealizationAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      π'.toRawCentral)
    (s : ℝ)
    (S : Set (AdelicGL2 (𝓞 F) F))
    (hpair :
      (∀ g : AdelicGL2 (𝓞 F) F, ∀ x y : AdelicGL2 (𝓞 F) F → ℂ,
        x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
        y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
        peterssonIntegral F s S (fun z => x (z * g)) (fun z => y (z * g)) =
          ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) *
            peterssonIntegral F s S x y) ∧
      peterssonIntegral F s S R'.toFun R'.toFun ≠ 0 ∧
      (R'.centralChar = R'.centralChar →
        (∀ g : AdelicGL2 (𝓞 F) F, ∀ x y : AdelicGL2 (𝓞 F) F → ℂ,
          x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) ⊔
              Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
          y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
          peterssonIntegral F s S (fun z => x (z * g)) (fun z => y (z * g)) =
            ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) *
              peterssonIntegral F s S x y) ∧
        ∃ P : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) →ₗ⋆[ℂ] ℂ,
          (∀ g : AdelicGL2 (𝓞 F) F, ∀ x y : AdelicGL2 (𝓞 F) F → ℂ,
            x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) ⊔
                Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
            y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
            P (fun z => x (z * g)) (fun z => y (z * g)) =
              ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * P x y) ∧
          (∃ y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)),
            P y y ≠ 0) ∧
          ∀ x y : AdelicGL2 (𝓞 F) F → ℂ,
            x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) ⊔
                Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
            y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
            P x y = peterssonIntegral F s S x y))
    (hnorm : ∀ v : HeightOneSpectrum (𝓞 F),
      ideleNorm F (uniformizerIdele F v) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ v : HeightOneSpectrum (𝓞 F),
      ‖π'.a v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖π'.b v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ := by sorry
