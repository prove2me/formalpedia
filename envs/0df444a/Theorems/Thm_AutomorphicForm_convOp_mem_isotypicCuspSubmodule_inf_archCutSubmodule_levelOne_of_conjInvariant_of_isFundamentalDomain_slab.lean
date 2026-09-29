-- Prove2me | Theorems.Thm_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_levelOne_of_conjInvariant_of_isFundamentalDomain_slab
-- name    : AutomorphicForm.convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_levelOne_of_conjInvariant_of_isFundamentalDomain_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/af9fed81-e2de-5b1f-8ae2-1b22be0828e4
-- title:
--   Right convolution stabilises cut isotypic cusp spaces (slab domain)
-- statement:
--   Let $L$ be a number field, let $0<\alpha<\beta$ be real numbers, and let $\Phi_L\subseteq \mathrm{GL}_2(\mathbb{A}_L)$ be contained in the determinant slab $\{g : \lVert\det g\rVert_{\mathbb{A}}\in[\alpha,\beta]\}$ (the idele norm being the module of multiplication by $\det g$ on $\mathbb{A}_L$) and be a measure-theoretic fundamental domain for the action of the image of $\mathrm{GL}_2(L)\to\mathrm{GL}_2(\mathbb{A}_L)$ on the Haar measure `adelicGLHaar` restricted to that slab. Let $\xi_L$ be a homomorphism from the full subgroup of $\mathbb{A}_L^\times$ to $\mathbb{C}^\times$, let $S$ be a finite set of finite places of $L$, let $N$ and $M$ be ideals of $\mathcal{O}_L$ all of whose prime divisors lie in $S$, let `tys` assign to each infinite place $w$ a finite list of finite-dimensional complex representations of `rowIsometrySubgroup₀ w.Completion`, and let $\Psi$ consist of a nonzero level ideal together with families $a,b$ of complex numbers indexed by the finite places. Write $U(M)$ for `principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L`. Let $g:\mathrm{GL}_2(\mathbb{A}_L)\to\mathbb{C}$ be continuous with compact support, satisfy $g(ux)=g(x)=g(xu)$ for all $u\in U(M)$ and all $x$, satisfy $g(\kappa x\kappa^{-1})=g(x)$ for every infinite place $w$ and every $\kappa$ in `rowIsometrySubgroup₀ w.Completion` placed at $w$ by `rowIsometryInclAt₀ L w`, and vanish at every $x$ whose finite component `glFin` is not the finite component of some element of $U(M)$. Let the carrier data be `productionPinsOf` at $\Phi_L$ with Borel structure and Haar measure on $\mathrm{GL}_2(\mathbb{A}_L)$, central subgroup $\top$, level groups $N\mapsto$ `levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L`, Hecke generators `heckeGen`, and the additive adelic Haar measure conditioned on `adelicBox L`. Then for every $u$ in the intersection of `isotypicCuspSubmodule` for these data, $\xi_L$, $N$, $S$, $\Psi$ — the complex span of the continuous functions that are smooth cusp automorphic for the carrier data and $\xi_L$, right invariant under the level group at $N$, Hecke coset eigenfunctions with eigenvalue $\Psi.a\,v$ for each $v\notin S$, and central eigenfunctions with eigenvalue $\Psi.b\,v$ for each $v\notin S$ — with the archimedean cut $\bigsqcap_w \bigsqcup_i$ of the type submodules of `tys`, the right convolution `convOp L g u`, namely $x\mapsto\int u(xy)\,g(y)\,dy$ against the Haar measure, again lies in that intersection.
--
--   This is the stability of a cut isotypic space of cusp forms of level `levelOne` at $N$ under right convolution by a conjugation-invariant kernel concentrated on the principal congruence level $M$, with $M$ allowed to differ from $N$. It serves as the block-stability input for the Hilbert–Schmidt style bound [`AutomorphicForm.forall_isCompact_exists_tsum_norm_finsum_twistedConvOp_mul_conj_le_of_orthonormal_of_isFundamentalDomain_slab`](thm.html#AutomorphicForm.forall_isCompact_exists_tsum_norm_finsum_twistedConvOp_mul_conj_le_of_orthonormal_of_isFundamentalDomain_slab), where a Galois twist transports the level of the kernel.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_levelOne_of_conjInvariant_of_isFundamentalDomain_slab.lean

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

theorem AutomorphicForm.convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_levelOne_of_conjInvariant_of_isFundamentalDomain_slab
    (L : Type) [Field L] [NumberField L]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (N : Ideal (𝓞 L)) (hN : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ S)
    (M : Ideal (𝓞 L)) (hM : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ M → w ∈ S)
    (tys : ArchTypeFamily L) (Ψ : HeckeEigensystem L ℂ)
    (g : AdelicGL2 (𝓞 L) L → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgU : IsBiInvariantUnder L (principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) g)
    (hgconj : ∀ (w : InfinitePlace L) (κ : rowIsometrySubgroup₀ w.Completion) (x : AdelicGL2 (𝓞 L) L),
      g (rowIsometryInclAt₀ L w κ * x * (rowIsometryInclAt₀ L w κ)⁻¹) = g x)
    (hgsupp : ∀ x : AdelicGL2 (𝓞 L) L, g x ≠ 0 →
      ∃ u ∈ principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L, glFin (𝓞 L) L u = glFin (𝓞 L) L x) :
    ∀ u ∈ isotypicCuspSubmodule L
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N S Ψ ⊓ archCutSubmodule L tys,
      convOp L g u ∈ isotypicCuspSubmodule L
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N S Ψ ⊓ archCutSubmodule L tys := by sorry
