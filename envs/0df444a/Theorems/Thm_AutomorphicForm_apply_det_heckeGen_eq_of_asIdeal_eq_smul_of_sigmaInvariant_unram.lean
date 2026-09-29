-- Prove2me | Theorems.Thm_AutomorphicForm_apply_det_heckeGen_eq_of_asIdeal_eq_smul_of_sigmaInvariant_unram
-- name    : AutomorphicForm.apply_det_heckeGen_eq_of_asIdeal_eq_smul_of_sigmaInvariant_unram
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/e68e66de-2eed-5f44-beed-2358614d8707
-- title:
--   σ-invariant idele characters agree at Hecke generators above v
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an algebra over $K$, and let $D$ be an [`M4aHerbrand.IdeleGaloisDescent`](def/M4aHerbrand_IdeleClassVocab.html#L28) datum for $(\mathcal{O}_L, K, L)$, that is, a monoid homomorphism $\mathrm{act}$ from $\mathrm{Aut}_K(L)$ to the ring automorphisms of the adele ring $\mathbb{A}_L$ which is compatible with the structure map $L \to \mathbb{A}_L$ (each $\mathrm{act}(g)$ restricts to $g$ on $L$) and continuous in each $g$. Fix $\sigma \in \mathrm{Aut}_K(L)$ and a character $\xi_L$, i.e. a monoid homomorphism from the full subgroup of $\mathbb{A}_L^\times$ to $\mathbb{C}^\times$, satisfying $\xi_L(\mathrm{unitsAct}\,D\,\sigma\,(z_0)) = \xi_L(z_0)$ for every idele unit $z_0$, where $\mathrm{unitsAct}$ is the automorphism of $\mathbb{A}_L^\times$ induced by $\mathrm{act}(\sigma)$. Let $v$ be a height one prime of $\mathcal{O}_K$ and $w$ a prime of $\mathcal{O}_L$ together with a proof that it lies under $v$. Assume that every prime $w_2$ of $\mathcal{O}_L$ lying under $v$ has $\mathrm{ramificationIdx}'$ of $v$'s ideal in $w_2$'s ideal equal to $1$. Let $w'$ be a prime of $\mathcal{O}_L$ whose ideal is the pointwise image $\sigma \cdot \mathfrak{p}_w$. Assume finally that the semi-local character $\mathrm{TwistedUnipotentTerm.semiLocalCharacter}\,K\,L\,\xi_L\,v$ — the finite product over the primes $w''$ of $\mathcal{O}_L$ above $v$ of $\xi_L$ applied to $\det$ of the Hecke element $\mathrm{heckeGenAt}$ at $w''$ evaluated on the $w''$-component of $\zeta$ under the base-change isomorphism — takes the value $1$ at every $\zeta$ in $\mathrm{integralUnits}\,K\,L\,v$, the group of units of $L \otimes_K K_v$ lying in the range of the map $\mathcal{O}_L \otimes_{\mathcal{O}_K} \mathcal{O}_v \to L \otimes_K K_v$. Then the complex numbers $\xi_L(\det \mathrm{heckeGen}(\mathcal{O}_L, L, w'))$ and $\xi_L(\det \mathrm{heckeGen}(\mathcal{O}_L, L, w))$ coincide, where $\mathrm{heckeGen}$ at a prime is the image in $\mathrm{GL}_2(\mathbb{A}_L)$ of the diagonal element with the canonical uniformiser unit at that prime in the first entry and $1$ elsewhere.
--
--   This is the transport of the value of an idele character at a local Hecke generator along a $K$-automorphism $\sigma$ of $L$: for a $\sigma$-invariant character that is trivial on the integral units above $v$, the Hecke generators at $w$ and at the conjugate prime $\sigma \cdot \mathfrak{p}_w$ give the same value. It feeds the unramified branch of [`AutomorphicForm.exists_forall_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_weighted_moments_unram`](thm.html#AutomorphicForm.exists_forall_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_weighted_moments_unram), and its proof invokes the uniqueness of the idele Galois descent datum ([`M4aHerbrand.subsingleton_ideleGaloisDescent`](thm.html#M4aHerbrand.subsingleton_ideleGaloisDescent)) together with the explicit description of the genuine datum on finite and infinite components.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_apply_det_heckeGen_eq_of_asIdeal_eq_smul_of_sigmaInvariant_unram.lean

import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped Pointwise TensorProduct

theorem AutomorphicForm.apply_det_heckeGen_eq_of_asIdeal_eq_smul_of_sigmaInvariant_unram
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξσ : ∀ z₀ : (AdeleRing (𝓞 L) L)ˣ,
      ξL ⟨M4aHerbrand.IdeleGaloisDescent.unitsAct D σ z₀, Subgroup.mem_top _⟩ = ξL ⟨z₀, Subgroup.mem_top z₀⟩)
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (hunr : ∀ w₂ : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w₂ = v →
      (HeightOneSpectrum.under (𝓞 K) w₂).asIdeal.ramificationIdx' w₂.asIdeal = 1)
    (w' : HeightOneSpectrum (𝓞 L)) (hw' : w'.asIdeal = σ • w.1.asIdeal)
    (hξv : ∀ ζ ∈ AutomorphicForm.TransversalMeasure.integralUnits K L v,
      TwistedUnipotentTerm.semiLocalCharacter K L ξL v ζ = 1) :
    ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w'), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) =
      ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w.1), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) := by sorry
