-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_pow
-- name    : AlgebraicGeometry.OModulePresheaf.isQuasicoherent_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/be43f5e3-afa4-56aa-97a5-713832c64ab8
-- title:
--   Finite direct powers preserve quasi-coherence of module presheaves
-- statement:
--   Let $R$ be a commutative ring, $V$ a scheme and $\pi\colon V \to \operatorname{Spec} R$ a morphism, and let $F$ be an `OModulePresheaf` over $\pi$: a datum assigning to each open $U \subseteq V$ an abelian group $F.\mathrm{obj}\,U$ carrying both an $R$-module structure and a $\Gamma(V,U)$-module structure, compatible as a scalar tower via the $R$-algebra structure on $\Gamma(V,U)$ coming from $\pi$, together with $R$-linear restriction maps $F.\mathrm{res}\colon F.\mathrm{obj}\,U' \to F.\mathrm{obj}\,U$ for $U \le U'$ which are semilinear for the restriction of sections, and which are the identity for $U = U'$ and compose along nested inclusions. Let $n$ be a natural number and assume $F$ is quasi-coherent in the sense of `IsQuasicoherent`: for every affine open $U$ of $V$ and every $f \in \Gamma(V,U)$, (i) every element $x$ of $F.\mathrm{obj}(V.\mathrm{basicOpen}\,f)$ satisfies $F.\mathrm{res}\,y = (f^m|_{D(f)}) \cdot x$ for some exponent $m$ and some $y \in F.\mathrm{obj}\,U$, and (ii) every $y \in F.\mathrm{obj}\,U$ whose restriction to $V.\mathrm{basicOpen}\,f$ vanishes is annihilated by $f^m$ for some $m$. The conclusion is that the $n$-th power datum `F.pow n`, given by $U \mapsto (\mathrm{Fin}\,n \to F.\mathrm{obj}\,U)$ with the pointwise module structures and componentwise restriction, is again quasi-coherent in the same sense.
--
--   This is the closure of the elementwise, basic-open formulation of quasi-coherence under passage to finite direct powers of module-presheaf data over a morphism to an affine base. It is used in the Čech-theoretic finiteness arguments for quasi-coherent data, being cited in the proof of [`AlgebraicGeometry.OModulePresheaf.exists_affHom_cechPushforward_comp_eq_of_forall_ker_eq_pow_smul_top_of_isProper`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_affHom_cechPushforward_comp_eq_of_forall_ker_eq_pow_smul_top_of_isProper).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_pow.lean

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.Away.Basic
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.isQuasicoherent_pow {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} {F : OModulePresheaf π} (n : ℕ) (hF : F.IsQuasicoherent) : (F.pow n).IsQuasicoherent := by sorry
