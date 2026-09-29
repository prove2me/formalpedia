-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_principalLevel_of_isBiInvariantUnder_of_isFundamentalDomain_slab
-- name    : AutomorphicForm.exists_forall_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_principalLevel_of_isBiInvariantUnder_of_isFundamentalDomain_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/8d16cfd0-81cb-52ee-9482-e17926906b18
-- title:
--   Twisted convolution carries isotypic cut blocks to a transported block
-- statement:
--   Let $K \subseteq L$ be number fields, let $D$ be an idele Galois descent datum for $L/K$ (a homomorphism from $\mathrm{Aut}_K(L)$ to continuous ring automorphisms of $\mathbb{A}_L$ extending the action on principal adeles), and let $\sigma$ be a $K$-automorphism of $L$. Let $0 < \alpha < \beta$ and let $\Phi_L \subseteq \mathrm{GL}_2(\mathbb{A}_L)$ be contained in the determinant slab $\{g : \lVert \det g\rVert \in [\alpha,\beta]\}$, where $\lVert\cdot\rVert$ is the idele norm given by the distinguished Haar character, and be a fundamental domain for the image of $\mathrm{GL}_2(L)$ acting on the adelic Haar measure of $\mathrm{GL}_2(\mathbb{A}_L)$ restricted to that slab. Let $\xi_L$ be a character of the full idele group $\mathbb{A}_L^\times$ with $\xi_L \circ (D.\mathrm{act}\,\sigma) = \xi_L$ on units; let $S_L$ be a finite set of finite places of $L$ whose membership depends only on the place of $K$ below, and $N$ an ideal of $\mathcal{O}_L$ all of whose prime divisors lie in $S_L$; let $\mathrm{tys}_L$ assign to each infinite place $w$ of $L$ finitely many complex representations of the row-isometry subgroup at $w$; and let $\Psi$ be a Hecke eigensystem over $\mathbb{C}$ (nonzero level together with coefficient functions $a$, $b$ on finite places) of level $N$. Then there exists a Hecke eigensystem $\Psi'$ of level $N$ with $\Psi'.a\,w = \Psi'.b\,w = 0$ for all $w \in S_L$ such that, for every continuous compactly supported $\varphi : \mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C}$ which is bi-invariant under the principal level subgroup of level $N$ intersected with the finite-adelic subgroup and satisfies $g \mapsto \varphi(g^{-1})$ lies in the archimedean cut submodule of $\mathrm{tys}_L$ while $\varphi$ lies in the archimedean dual cut submodule, and for every $u$ in the intersection of the archimedean cut submodule with the isotypic cusp submodule for $\xi_L$, $N$, $S_L$, $\Psi$ (the span of the continuous functions that are smooth cusp automorphic for the production pins at $\Phi_L$ with level family $M \mapsto$ principal level $M$ intersected with the finite-adelic subgroup, Hecke generators $\mathrm{heckeGen}$ and conditioning box the adelic box, right invariant under the level-$N$ subgroup, Hecke coset eigenfunctions with eigenvalue $\Psi.a\,v$ outside $S_L$ and central eigenfunctions with eigenvalue $\Psi.b\,v$ there), the twisted convolution $g \mapsto \int u(\sigma_{\mathbb{A}}(g x))\,\varphi(x)\,dx$ lies in the corresponding intersection taken with $\Psi'$ in place of $\Psi$.
--
--   This is the stability of the $\sigma$-twisted convolution operators on a single archimedean-cut isotypic block of automorphic forms: the block attached to one Hecke eigensystem $\Psi$ is carried into the block attached to a single transported eigensystem $\Psi'$ of the same level, whose data are annihilated on the ramified set $S_L$. It supplies the operator-level input for the twisted trace computations on the cut blocks, where the traces of these operators are compared with the corresponding untwisted quantities.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_principalLevel_of_isBiInvariantUnder_of_isFundamentalDomain_slab.lean

import Definitions.Def_AutomorphicForm_UnitFactorizableOfType
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_forall_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_principalLevel_of_isBiInvariantUnder_of_isFundamentalDomain_slab
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξσ : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      ξL ⟨Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
          AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L) z, Subgroup.mem_top _⟩ =
        ξL ⟨z, Subgroup.mem_top z⟩)
    (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w w' : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (w ∈ SL ↔ w' ∈ SL))
    (N : Ideal (𝓞 L)) (hN : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ SL)
    (tysL : ArchTypeFamily L)
    (Ψ : HeckeEigensystem L ℂ) (hΨN : Ψ.level = N) :
    ∃ Ψ' : HeckeEigensystem L ℂ, Ψ'.level = N ∧ (∀ w ∈ SL, Ψ'.a w = 0 ∧ Ψ'.b w = 0) ∧
      ∀ (φ : AdelicGL2 (𝓞 L) L → ℂ), Continuous φ → HasCompactSupport φ →
        IsBiInvariantUnder L (principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) φ →
        IsArchBiFinite L tysL φ →
      ∀ u ∈ isotypicCuspSubmodule L
            (productionPinsOf L ΦL (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun v => heckeGen (𝓞 L) L v) (adelicBox L)) ξL N SL Ψ ⊓ archCutSubmodule L tysL,
        twistedConvOp K L D σ φ u ∈ isotypicCuspSubmodule L
            (productionPinsOf L ΦL (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun v => heckeGen (𝓞 L) L v) (adelicBox L)) ξL N SL Ψ' ⊓ archCutSubmodule L tysL := by sorry
