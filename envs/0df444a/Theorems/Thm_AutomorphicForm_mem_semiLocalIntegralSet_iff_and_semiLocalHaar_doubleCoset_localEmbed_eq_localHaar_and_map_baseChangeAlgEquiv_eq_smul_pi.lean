-- Prove2me | Theorems.Thm_AutomorphicForm_mem_semiLocalIntegralSet_iff_and_semiLocalHaar_doubleCoset_localEmbed_eq_localHaar_and_map_baseChangeAlgEquiv_eq_smul_pi
-- name    : AutomorphicForm.mem_semiLocalIntegralSet_iff_and_semiLocalHaar_doubleCoset_localEmbed_eq_localHaar_and_map_baseChangeAlgEquiv_eq_smul_pi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/ee2cacac-fb3d-5f32-997d-88b5114d7815
-- title:
--   Semi-local GL₂ above a finite place splits over w∣ v
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $v$ be a nonzero prime of $\mathcal{O}_K$, and assume the set $v.\mathrm{Extension}(\mathcal{O}_L)$ of primes $w$ of $\mathcal{O}_L$ lying under-$v$ is finite. Write $e$ for the $L$-algebra isomorphism `baseChangeAlgEquiv` from $L\otimes_K K_v$ onto $\prod_{w\mid v} L_w$, and for $g\in\mathrm{GL}_2(L\otimes_K K_v)$ let $g_w$ denote the image of $g$ under the entrywise map induced by $e$ followed by evaluation at $w$. Let $\mathcal{K}_v$ be the set of $g$ with $g$ and $g^{-1}$ entrywise in the semi-local integers, $\mathcal{K}_w$ the set of $\gamma\in\mathrm{GL}_2(L_w)$ with $\gamma,\gamma^{-1}$ entrywise in $\mathcal{O}_{L_w}$, and $\mu'_v$, $\mu_w$ the Haar measures of $\mathrm{GL}_2(L\otimes_K K_v)$, $\mathrm{GL}_2(L_w)$ normalised to give these sets measure $1$. For $w_0\mid v$ and $\rho\in\mathrm{GL}_2(L_{w_0})$ let $\tilde\rho\in\mathrm{GL}_2(L\otimes_K K_v)$ be the semi-local component of the finite-adelic matrix obtained by splicing $\rho$ into the identity matrix at $w_0$. The conclusion is the conjunction of five assertions: (1) $g\in\mathcal{K}_v$ iff $g_w\in\mathcal{K}_w$ for all $w\mid v$; (2) $\tilde\rho_{w_0}=\rho$ and $\tilde\rho_w=1$ for $w\neq w_0$; (3) $g\in\mathcal{K}_v\tilde\rho\,\mathcal{K}_v$ iff $g_{w_0}\in\mathcal{K}_{w_0}\rho\,\mathcal{K}_{w_0}$ and $g_w\in\mathcal{K}_w$ for all $w\neq w_0$; (4) $\mu'_v(\mathcal{K}_v\tilde\rho\,\mathcal{K}_v)=\mu_{w_0}(\mathcal{K}_{w_0}\rho\,\mathcal{K}_{w_0})$; and (5) for any Borel measurable structures on $L\otimes_K K_v$ and on the $L_w$, any additive Haar measure $\nu$ on $L\otimes_K K_v$ and any family of additive Haar measures $\nu_w$, there is $c\in(0,\infty)$ with $e_*\nu=c\cdot\prod_w\nu_w$.
--
--   This is the comparison between the semi-local group $\mathrm{GL}_2(L\otimes_K K_v)$ and the product of the local groups $\mathrm{GL}_2(L_w)$ over the places $w$ of $L$ above $v$, at the level of maximal compact subgroups, double cosets, normalised Haar volumes and additive Haar measures. It is the bookkeeping used when a local factor at a place of the base field is decomposed into the factors at the places of the extension, and it feeds the computations of orbital integrals and double-coset volumes for the semi-local Haar measure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_mem_semiLocalIntegralSet_iff_and_semiLocalHaar_doubleCoset_localEmbed_eq_localHaar_and_map_baseChangeAlgEquiv_eq_smul_pi.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AdelicDock_LocalEmbedding

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions Pointwise ENNReal

theorem AutomorphicForm.mem_semiLocalIntegralSet_iff_and_semiLocalHaar_doubleCoset_localEmbed_eq_localHaar_and_map_baseChangeAlgEquiv_eq_smul_pi
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) [Fintype (v.Extension (𝓞 L))] :
    (∀ g : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      g ∈ AutomorphicForm.semiLocalIntegralSet K L v ↔
        ∀ w : v.Extension (𝓞 L),
          Matrix.GeneralLinearGroup.map
              ((Pi.evalRingHom (fun w' : v.Extension (𝓞 L) => w'.1.adicCompletion L) w).comp
                (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v :
                  L ⊗[K] v.adicCompletion K →+* Π w' : v.Extension (𝓞 L), w'.1.adicCompletion L)) g ∈
            AutomorphicForm.localIntegralSet L w.1) ∧
    (∀ (w₀ : v.Extension (𝓞 L)) (ρ : GL (Fin 2) (w₀.1.adicCompletion L)),
      Matrix.GeneralLinearGroup.map
          ((Pi.evalRingHom (fun w' : v.Extension (𝓞 L) => w'.1.adicCompletion L) w₀).comp
            (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v :
              L ⊗[K] v.adicCompletion K →+* Π w' : v.Extension (𝓞 L), w'.1.adicCompletion L))
          (AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w₀.1 ρ)) = ρ ∧
      ∀ w : v.Extension (𝓞 L), w ≠ w₀ →
        Matrix.GeneralLinearGroup.map
            ((Pi.evalRingHom (fun w' : v.Extension (𝓞 L) => w'.1.adicCompletion L) w).comp
              (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v :
                L ⊗[K] v.adicCompletion K →+* Π w' : v.Extension (𝓞 L), w'.1.adicCompletion L))
            (AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w₀.1 ρ)) = 1) ∧
    (∀ (w₀ : v.Extension (𝓞 L)) (ρ : GL (Fin 2) (w₀.1.adicCompletion L))
        (g : GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
      g ∈ AutomorphicForm.semiLocalIntegralSet K L v *
            {AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w₀.1 ρ)} *
          AutomorphicForm.semiLocalIntegralSet K L v ↔
        Matrix.GeneralLinearGroup.map
              ((Pi.evalRingHom (fun w' : v.Extension (𝓞 L) => w'.1.adicCompletion L) w₀).comp
                (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v :
                  L ⊗[K] v.adicCompletion K →+* Π w' : v.Extension (𝓞 L), w'.1.adicCompletion L)) g ∈
            AutomorphicForm.localIntegralSet L w₀.1 * ({ρ} : Set (GL (Fin 2) (w₀.1.adicCompletion L))) *
              AutomorphicForm.localIntegralSet L w₀.1 ∧
          ∀ w : v.Extension (𝓞 L), w ≠ w₀ →
            Matrix.GeneralLinearGroup.map
                ((Pi.evalRingHom (fun w' : v.Extension (𝓞 L) => w'.1.adicCompletion L) w).comp
                  (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v :
                    L ⊗[K] v.adicCompletion K →+* Π w' : v.Extension (𝓞 L), w'.1.adicCompletion L)) g ∈
              AutomorphicForm.localIntegralSet L w.1) ∧
    (∀ (w₀ : v.Extension (𝓞 L)) (ρ : GL (Fin 2) (w₀.1.adicCompletion L)),
      AutomorphicForm.semiLocalHaar K L v
          (AutomorphicForm.semiLocalIntegralSet K L v *
              {AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w₀.1 ρ)} *
            AutomorphicForm.semiLocalIntegralSet K L v) =
        AutomorphicForm.localHaar L w₀.1
          (AutomorphicForm.localIntegralSet L w₀.1 * ({ρ} : Set (GL (Fin 2) (w₀.1.adicCompletion L))) *
            AutomorphicForm.localIntegralSet L w₀.1)) ∧
    (∀ [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
        [∀ w : v.Extension (𝓞 L), MeasurableSpace (w.1.adicCompletion L)]
        [∀ w : v.Extension (𝓞 L), BorelSpace (w.1.adicCompletion L)]
        (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure]
        (νw : ∀ w : v.Extension (𝓞 L), Measure (w.1.adicCompletion L)) [∀ w, (νw w).IsAddHaarMeasure],
      ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
        Measure.map (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v) ν = c • Measure.pi νw) := by sorry
