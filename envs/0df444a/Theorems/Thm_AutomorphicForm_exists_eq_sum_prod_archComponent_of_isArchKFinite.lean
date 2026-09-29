-- Prove2me | Theorems.Thm_AutomorphicForm_exists_eq_sum_prod_archComponent_of_isArchKFinite
-- name    : AutomorphicForm.exists_eq_sum_prod_archComponent_of_isArchKFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/dfa8890e-c3ef-5758-a535-9ef9a78b1dbf
-- title:
--   Arch-K-finite forms on K_∞ as sums of local products
-- statement:
--   Let $F$ be a number field, and let $\mu,\nu$ be group homomorphisms from the units of the adele ring $\mathbb{A}_F$ of $F$ to $\mathbb{C}^\times$, each assumed continuous as a $\mathbb{C}$-valued function. Let $U\colon \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be continuous and arch-$K$-finite, i.e. for every infinite place $w$ of $F$ there is a finite set $s$ of functions such that for every $k$ in the subgroup `archRowIsometrySubgroup F w` the translate $x\mapsto U(xk)$ lies in the $\mathbb{C}$-span of $s$. Assume moreover that $U$ transforms by $\mu\otimes\nu$ under the relevant Borel elements: for every $b\in\mathrm{GL}_2(\mathbb{A}_F)$ with lower-left entry $0$ whose finite component is $1$ and whose archimedean component at each infinite place $w$ is a row isometry (determinant of norm $1$, and the two rows act isometrically for the norm $\|x\|^2+\|y\|^2$), one has $U(bg)=\mu(b_{00})\,\nu(b_{11})\,U(g)$ for all $g$, where $b_{00},b_{11}$ denote the diagonal entries of $b$ viewed as units. The conclusion produces $m\in\mathbb{N}$ and functions $f_{j,w}\colon \mathrm{GL}_2(F_w)\to\mathbb{C}$ for $j\in\{0,\dots,m-1\}$ and $w$ infinite, such that: each $f_{j,w}$ is continuous; each $f_{j,w}$ is right finite for the subgroup of row isometries of $\mathrm{GL}_2(F_w)$, in the same sense of a finite spanning set for its right translates; for each $j,w$ and each $b\in\mathrm{GL}_2(F_w)$ with lower-left entry $0$ that is a row isometry and each row isometry $g$, one has $f_{j,w}(bg)=\mu_w(b_{00})\,\nu_w(b_{11})\,f_{j,w}(g)$, where $\mu_w,\nu_w$ are the local characters obtained by composing $\mu,\nu$ with the map from $F_w^\times$ to the ideles; and for every $k$ in the adelic maximal compact subgroup (finite component in `finiteIntegralGL2`, archimedean components row isometries) with trivial finite component, $U(k)=\sum_j\prod_w f_{j,w}(k_w)$, $k_w$ being the component of $k$ at $w$. Note that the local transformation law is asserted only for $b$ and $g$ both row isometries, not on all of $\mathrm{GL}_2(F_w)$.
--
--   This is the archimedean instance of the statement that a $K$-finite vector for a finite product of commuting compact groups is a finite sum of pure tensors of $K_w$-finite vectors, refined so that each local factor retains the transformation law under the upper-triangular elements of $K_w$. It feeds the factorisation of global zeta integrals attached to such a form, being cited by [`AutomorphicForm.exists_sum_mul_prod_localZeta_bottomRow_eq_of_isArchKFinite`](thm.html#AutomorphicForm.exists_sum_mul_prod_localZeta_bottomRow_eq_of_isArchKFinite).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_eq_sum_prod_archComponent_of_isArchKFinite.lean

import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain

theorem AutomorphicForm.exists_eq_sum_prod_archComponent_of_isArchKFinite
    (F : Type) [Field F] [NumberField F]
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (_hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
    (_hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
    (U : AdelicGL2 (𝓞 F) F → ℂ) (_hUc : Continuous U) (_hUK : IsArchKFinite F U)
    (_hUB : ∀ (b : AdelicGL2 (𝓞 F) F) (hb : b ∈ adelicBorel (𝓞 F) F),
        glFin (𝓞 F) F b = 1 →
        (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F b))) →
        ∀ g : AdelicGL2 (𝓞 F) F,
          U (b * g) = ((μ (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)
            * ((ν (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ) * U g) :
    ∃ (m : ℕ) (f : Fin m → (w : InfinitePlace F) → GL (Fin 2) w.Completion → ℂ),
      (∀ j w, Continuous (f j w)) ∧
      (∀ j w, RightTranslatesSpanFinite (rowIsometrySubgroup w.Completion) (f j w)) ∧
      (∀ (j : Fin m) (w : InfinitePlace F) (b : GL (Fin 2) w.Completion) (hb : b ∈ borelSubgroup w.Completion),
        IsRowIsometry b → ∀ g : GL (Fin 2) w.Completion, IsRowIsometry g →
          f j w (b * g) = ((archLocalChar μ w (borelDiagFst (⟨b, hb⟩ : ↥(borelSubgroup w.Completion))) : ℂˣ) : ℂ)
            * ((archLocalChar ν w (borelDiagSnd (⟨b, hb⟩ : ↥(borelSubgroup w.Completion))) : ℂˣ) : ℂ)
            * f j w g) ∧
      ∀ k : AdelicGL2 (𝓞 F) F, k ∈ adelicMaximalCompact F → glFin (𝓞 F) F k = 1 →
        U k = ∑ j, ∏ w, f j w (archComponent F w (glArch (𝓞 F) F k)) := by sorry
