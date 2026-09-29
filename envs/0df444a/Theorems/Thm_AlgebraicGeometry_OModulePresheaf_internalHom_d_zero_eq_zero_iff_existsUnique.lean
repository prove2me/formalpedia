-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique
-- name    : AlgebraicGeometry.OModulePresheaf.internalHom_d_zero_eq_zero_iff_existsUnique
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/25a00c8c-7c12-54c2-8268-150c7b017cc3
-- title:
--   Degree-zero sheaf condition for the internal Hom
-- statement:
--   Fix a commutative ring $R$, a scheme $V$ and a morphism $\pi : V \to \operatorname{Spec} R$, and let $F, G$ be module data on the opens of $V$ over $\pi$ (an abelian group $F(U)$ for each open $U$, carrying an $R$-module and a $\Gamma(V,U)$-module structure compatible via the $R$-algebra structure on $\Gamma(V,U)$ coming from $\pi$, together with $R$-linear restrictions that are semilinear over the restriction maps of $\mathcal O_V$ and functorial). Assume $G$ is quasi-coherent in the elementwise sense: for every affine open $U \subseteq V$ and every $f \in \Gamma(V,U)$, each element of $G(V_f)$ becomes, after multiplication by the restriction of some power $f^n$, the restriction of an element of $G(U)$, and any element of $G(U)$ restricting to $0$ in $G(V_f)$ is killed by some power $f^n$. Let $K$ be an ordered affine cover of $V$: a finite linearly ordered index type $\iota$ together with affine opens $U_i$ with $\bigsqcup_i U_i = \top$. Recall that a section of $\mathcal{H}om(F,G)$ over an open $U$ is a family $(\varphi_W)_W$, indexed by the affine opens $W \subseteq U$, of $R$-linear maps $F(W) \to G(W)$ that are $\Gamma(V,W)$-linear and commute with restriction along inclusions $W \subseteq W'$ of affine opens below $U$; restriction forgets components. Let $c$ be a Čech $0$-cochain for $K$ with values in $\mathcal{H}om(F,G)$, i.e. a family assigning to each strictly monotone $s : \mathrm{Fin}\,1 \to \iota$ a section of $\mathcal{H}om(F,G)$ over $\bigsqcap_j U_{s(j)}$. Then the degree-$0$ Čech differential of $c$ vanishes if and only if there is exactly one global section $\varphi$ of $\mathcal{H}om(F,G)$ over $\top$ whose restriction to each of these opens is $c\,s$.
--
--   This is the sheaf axiom in degree $0$ for the internal Hom module datum $\mathcal{H}om(F,G)$ relative to a finite ordered affine cover: exactness of $0 \to \mathcal{H}om(F,G)(V) \to \prod_i \mathcal{H}om(F,G)(U_i) \to \prod_{i<j} \mathcal{H}om(F,G)(U_i \cap U_j)$, with only the target $G$ assumed quasi-coherent. It supplies the degree-zero gluing step for the descent arguments `existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper` and `exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafInternalHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.internalHom_d_zero_eq_zero_iff_existsUnique
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} {F G : OModulePresheaf π}
    (hGq : G.IsQuasicoherent) (K : V.OrderedAffineCover) (c : (OModulePresheaf.internalHom F G).cochain K 0) :
    (OModulePresheaf.internalHom F G).d K 0 c = 0 ↔
      ∃! φ : (OModulePresheaf.internalHom F G).obj ⊤,
        ∀ s : K.Idx 0, c s = (OModulePresheaf.internalHom F G).res le_top φ := by sorry
