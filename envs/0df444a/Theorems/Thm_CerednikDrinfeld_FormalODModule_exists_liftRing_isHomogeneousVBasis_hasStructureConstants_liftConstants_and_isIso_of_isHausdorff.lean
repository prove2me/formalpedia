-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_liftRing_isHomogeneousVBasis_hasStructureConstants_liftConstants_and_isIso_of_isHausdorff
-- name    : CerednikDrinfeld.FormalODModule.exists_liftRing_isHomogeneousVBasis_hasStructureConstants_liftConstants_and_isIso_of_isHausdorff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/805bc354-f0e1-5db1-a2bd-4d8c30e3ca3b
-- title:
--   Formal mathcal O_D-modules lift to the universal p-torsion-free base
-- statement:
--   Let $p$ be a prime, $B$ a commutative ring and $j \colon \mathbb Z_{p^2} = W(\mathbb F_{p^2}) \to B$ a ring homomorphism, and assume $B$ is Hausdorff for the ideal $(p)$. Let $X$ be a formal $\mathcal O_D$-module over $B$: a commutative two-dimensional formal group law $X.F$ together with an action of $\mathbb Z_{p^2}$ by endomorphisms of the law and an endomorphism $\varpi$ with $\varpi \circ \varpi = [p]$ and $\varpi \circ [a] = [\mathrm{Frob}(a)] \circ \varpi$. Let $\gamma \colon \mathrm{Fin}\,2 \to \mathrm{Cart}_p(X.F)$ be a homogeneous $V$-basis relative to $j$, i.e. each $\gamma_i$ satisfies $[\tau(c)]_*\gamma_i = j(\tau(c))^{p^i}\cdot\gamma_i$ for every $c \in \mathbb F_{p^2}$ (Teichmüller representatives $\tau$, homothety on the right) and the matrix of tangent vectors $(\mathrm{tangent}(\gamma_i)_k)_{i,k}$ has unit determinant. Let $a \colon \mathbb N \to \mathrm{Fin}\,2 \to B$ be structure constants for $\gamma$: for all $i$ and all $N$, $\varpi_*\gamma_i = \sum_{m<N} V^m\big(a_{m,i}\cdot\gamma_{\pi(m,i)}\big) + V^N h$ for some $h$, where $V$ is the integral Verschiebung and $\pi(m,i) \equiv m+i+1 \pmod 2$; assume $a_{0,0}a_{0,1} = p$. Put $S = \mathbb Z_{p^2}[X_b : b \in B]/(X_{a_{0,0}}X_{a_{0,1}} - p)$, with the surjection $\lambda \colon S \to B$ extending $j$ by $X_b \mapsto b$. Then there exist a formal $\mathcal O_D$-module $X_\ell$ over $S$ and $\gamma_\ell \colon \mathrm{Fin}\,2 \to \mathrm{Cart}_p(X_\ell.F)$ which is a homogeneous $V$-basis relative to the structure map $\mathbb Z_{p^2} \to S$ and has structure constants the classes of $X_{a_{m,i}}$, together with an isomorphism $u$ of formal $\mathcal O_D$-modules over $B$ from the base change of $X_\ell$ along $\lambda$ to $X$ such that $u_*$ carries the base change of each $\gamma_{\ell,i}$ to $\gamma_i$.
--
--   This is the lifting step in the Cerednik–Drinfeld uniformisation: a formal $\mathcal O_D$-module with a homogeneous $V$-basis over an arbitrary ($p$-adically Hausdorff) base is obtained by base change from one over the explicit ring $S$, which is $p$-torsion-free. It is used in the construction of the canonical $L$-map to the graded Cartier-module data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_liftRing_isHomogeneousVBasis_hasStructureConstants_liftConstants_and_isIso_of_isHausdorff.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.FormalODModule.exists_liftRing_isHomogeneousVBasis_hasStructureConstants_liftConstants_and_isIso_of_isHausdorff
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (hsep : IsHausdorff (Ideal.span {(p : B)}) B)
    (X : CerednikDrinfeld.FormalODModule p B)
    (γ : Fin 2 → MvFormalGroup.CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (a : ℕ → Fin 2 → B) (ha : X.HasStructureConstants γ a) (h01 : a 0 0 * a 0 1 = (p : B)) :
    ∃ (Xl : CerednikDrinfeld.FormalODModule p
          (CerednikDrinfeld.CartierLift.LiftRing p (CerednikDrinfeld.Zp2 p) (a 0 0) (a 0 1)))
      (γl : Fin 2 → MvFormalGroup.CartierModule p Xl.F),
      Xl.IsHomogeneousVBasis
          (algebraMap (CerednikDrinfeld.Zp2 p)
            (CerednikDrinfeld.CartierLift.LiftRing p (CerednikDrinfeld.Zp2 p) (a 0 0) (a 0 1))) γl ∧
        Xl.HasStructureConstants γl
          (CerednikDrinfeld.CartierLift.liftConstants (p := p) (R := CerednikDrinfeld.Zp2 p) a) ∧
        ∃ u : (Xl.map (CerednikDrinfeld.CartierLift.liftHom j (a 0 0) (a 0 1) h01)).Hom X,
          u.IsIso ∧ ∀ i : Fin 2,
            MvFormalGroup.CartierModule.map u.toLawHom
              (MvFormalGroup.CartierModule.baseChange
                (CerednikDrinfeld.CartierLift.liftHom j (a 0 0) (a 0 1) h01) (γl i)) = γ i := by sorry
