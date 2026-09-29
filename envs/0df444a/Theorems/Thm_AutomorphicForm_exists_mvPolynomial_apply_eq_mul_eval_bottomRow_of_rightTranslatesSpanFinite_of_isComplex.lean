-- Prove2me | Theorems.Thm_AutomorphicForm_exists_mvPolynomial_apply_eq_mul_eval_bottomRow_of_rightTranslatesSpanFinite_of_isComplex
-- name    : AutomorphicForm.exists_mvPolynomial_apply_eq_mul_eval_bottomRow_of_rightTranslatesSpanFinite_of_isComplex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/5780fc18-98a1-502b-97b2-00c602a8bbf8
-- title:
--   Complex place: K-finite induced vectors are polynomials in the bottom row
-- statement:
--   Let $F$ be a field, $w$ an infinite place of $F$ that is complex, and write $F_w$ for the completion of $F$ at $w$ and $\iota_w =$ `extensionEmbedding w` for the canonical embedding $F_w \to \mathbb{C}$. Let $\eta_1,\eta_2 \colon F_w^\times \to \mathbb{C}^\times$ be group homomorphisms and let $f \colon \mathrm{GL}_2(F_w) \to \mathbb{C}$ be continuous. Call $k \in \mathrm{GL}_2(F_w)$ a row isometry if $\|\det k\| = 1$ and $\|x k_{00} + y k_{10}\|^2 + \|x k_{01} + y k_{11}\|^2 = \|x\|^2 + \|y\|^2$ for all $x,y \in F_w$; these form the subgroup `rowIsometrySubgroup`. Assume $f$ is right finite for this subgroup in the sense of `RightTranslatesSpanFinite`: there is one finite family $s$ of functions $\mathrm{GL}_2(F_w) \to \mathbb{C}$ such that $x \mapsto f(xk)$ lies in the $\mathbb{C}$-span of $s$ for every row isometry $k$. Assume further that $f(bg) = \eta_1(b_{00})\,\eta_2(b_{11})\,f(g)$ whenever $b$ lies in `borelSubgroup` (i.e. $b_{10} = 0$) and is a row isometry and $g$ is a row isometry, where $b_{00}$ and $b_{11}$ are viewed as units via `borelDiagFst` and `borelDiagSnd`. The conclusion is that there exists a polynomial $P \in \mathbb{C}[X_0,X_1,Y_0,Y_1]$, with variables indexed by `Fin 2 ⊕ Fin 2`, such that for every row isometry $k$, $$f(k) = \eta_1(\det k)\cdot P\bigl(\iota_w(k_{10}),\iota_w(k_{11}),\overline{\iota_w(k_{10})},\overline{\iota_w(k_{11})}\bigr),$$ the left summand of the index evaluating at the images of the bottom row entries $k_{1i}$ and the right summand at their complex conjugates.
--
--   This is the archimedean input at a complex place for the realisation of $K$-finite vectors of the representation induced from a pair of characters by explicit functions: on the maximal compact subgroup, such a vector is $\eta_1(\det)$ times a polynomial in the bottom row and its conjugate. It is used by [`AutomorphicForm.exists_sum_mul_localZeta_bottomRow_eq_of_rightTranslatesSpanFinite`](thm.html#AutomorphicForm.exists_sum_mul_localZeta_bottomRow_eq_of_rightTranslatesSpanFinite), where the bihomogeneous components of $P$ are integrated against a Gaussian along the bottom row to produce local zeta factors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_mvPolynomial_apply_eq_mul_eval_bottomRow_of_rightTranslatesSpanFinite_of_isComplex.lean

import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_BorelSubgroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.WindowedSiegel

theorem AutomorphicForm.exists_mvPolynomial_apply_eq_mul_eval_bottomRow_of_rightTranslatesSpanFinite_of_isComplex
    (F : Type) [Field F] (w : InfinitePlace F) (_hw : w.IsComplex)
    (η₁ η₂ : (w.Completion)ˣ →* ℂˣ)
    (f : GL (Fin 2) w.Completion → ℂ) (_hfc : Continuous f)
    (_hfK : RightTranslatesSpanFinite (rowIsometrySubgroup w.Completion) f)
    (_hfB : ∀ (b : GL (Fin 2) w.Completion) (hb : b ∈ borelSubgroup w.Completion), IsRowIsometry b →
        ∀ g : GL (Fin 2) w.Completion, IsRowIsometry g →
          f (b * g) = ((η₁ (borelDiagFst (⟨b, hb⟩ : ↥(borelSubgroup w.Completion))) : ℂˣ) : ℂ)
            * ((η₂ (borelDiagSnd (⟨b, hb⟩ : ↥(borelSubgroup w.Completion))) : ℂˣ) : ℂ) * f g) :
    ∃ P : MvPolynomial (Fin 2 ⊕ Fin 2) ℂ,
      ∀ k : GL (Fin 2) w.Completion, IsRowIsometry k →
        f k = ((η₁ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)
          * MvPolynomial.eval
              (Sum.elim (fun i => extensionEmbedding w ((k : Matrix (Fin 2) (Fin 2) w.Completion) 1 i))
                (fun i => starRingEnd ℂ
                  (extensionEmbedding w ((k : Matrix (Fin 2) (Fin 2) w.Completion) 1 i)))) P := by sorry
