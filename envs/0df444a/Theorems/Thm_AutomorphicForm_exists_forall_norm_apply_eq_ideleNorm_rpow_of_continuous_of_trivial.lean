-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_norm_apply_eq_ideleNorm_rpow_of_continuous_of_trivial
-- name    : AutomorphicForm.exists_forall_norm_apply_eq_ideleNorm_rpow_of_continuous_of_trivial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/226ce4fb-5a3b-5712-a40b-417ca2405431
-- title:
--   Modulus of an idele class character is a power of the norm
-- statement:
--   Let $K$ be a number field, with ring of integers $\mathcal O_K$ and adele ring $\mathbb A = \mathrm{AdeleRing}(\mathcal O_K,K)$. Let $\xi_K$ be a monoid homomorphism from the full subgroup $\top \le \mathbb A^\times$ to $\mathbb C^\times$, so in effect a character of $\mathbb A^\times$. Two hypotheses are imposed: the map $z \mapsto \xi_K(z) \in \mathbb C$, obtained by regarding every idele as an element of the top subgroup and composing with the inclusion $\mathbb C^\times \hookrightarrow \mathbb C$, is continuous; and $\xi_K(z) = 1$ for every $z$ lying in the range of the unit-group map induced by $K \to \mathbb A$, i.e. $\xi_K$ is trivial on the principal ideles. The conclusion is that there exists a real number $w$ such that for every $z \in \mathbb A^\times$ one has $\lVert \xi_K(z)\rVert = (\lvert z\rvert_{\mathbb A})^{w}$, a real power (`Real.rpow`) of $\lvert z\rvert_{\mathbb A} = \mathrm{ideleNorm}\,K\,z$, which is defined as the real number underlying the distributive Haar character $\mathrm{distribHaarChar}(\mathbb A)(z) \in \mathbb R_{\ge 0}$, that is, the modulus by which multiplication by $z$ scales Haar measure on $\mathbb A$.
--
--   This is the classical statement that the absolute value of a continuous idele class character of a number field is a real power of the idelic norm, the first step in separating a Hecke character into its unitary part and its exponent. It is used in the analytic estimates for automorphic forms on $\mathrm{GL}_2$ over the adeles, in particular in the results on convergence of the integrals and sums attached to the cuspidal spectrum that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_norm_apply_eq_ideleNorm_rpow_of_continuous_of_trivial.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_forall_norm_apply_eq_ideleNorm_rpow_of_continuous_of_trivial
    (K : Type) [Field K] [NumberField K]
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1) :
    ∃ w : ℝ, ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ) := by sorry
