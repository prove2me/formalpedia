-- Prove2me | Theorems.Thm_AutomorphicForm_exists_mvPolynomial_apply_eq_mul_eval_bottomRow_of_rightTranslatesSpanFinite_of_isReal
-- name    : AutomorphicForm.exists_mvPolynomial_apply_eq_mul_eval_bottomRow_of_rightTranslatesSpanFinite_of_isReal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/c3d78cba-a293-5861-857e-1b4527d2e0ff
-- title:
--   Polynomiality in the bottom row at a real place
-- statement:
--   Let $F$ be a field, $w$ an infinite place of $F$ with $w$ real, and $F_w$ the completion of $F$ at $w$, and let $\eta_1,\eta_2\colon F_w^{\times}\to\mathbb{C}^{\times}$ be group homomorphisms. Let $f\colon \mathrm{GL}_2(F_w)\to\mathbb{C}$ be a function subject to three hypotheses: $f$ is continuous; $f$ is right finite for the subgroup of row isometries, i.e. there is a finite family $s$ of functions $\mathrm{GL}_2(F_w)\to\mathbb{C}$ such that for every $k$ with $\lVert\det k\rVert=1$ and $\lVert xk_{00}+yk_{10}\rVert^{2}+\lVert xk_{01}+yk_{11}\rVert^{2}=\lVert x\rVert^{2}+\lVert y\rVert^{2}$ for all $x,y\in F_w$, the translate $x\mapsto f(xk)$ lies in the $\mathbb{C}$-span of $s$; and $f(bg)=\eta_1(b_{00})\,\eta_2(b_{11})\,f(g)$ whenever $b$ satisfies $b_{10}=0$ and both $b$ and $g$ are row isometries in the above sense (here $b_{00}$ and $b_{11}$ are regarded as units of $F_w$ via the two diagonal characters of the lower-left-zero subgroup). The conclusion is that there exists a polynomial $P$ in four variables over $\mathbb{C}$, the variables indexed by $\mathrm{Fin}\,2\sqcup\mathrm{Fin}\,2$, such that for every row isometry $k$ one has $f(k)=\eta_1(\det k)\cdot P$ evaluated at the assignment sending the $i$-th variable of the first copy to $\iota_w(k_{1i})$ and the $i$-th variable of the second copy to $\overline{\iota_w(k_{1i})}$, where $\iota_w\colon F_w\to\mathbb{C}$ is the canonical embedding.
--
--   This is the archimedean real-place input behind Lemma 5.13 of Jacquet–Langlands: on the maximal compact subgroup at a real place, a $K$-finite vector in the representation induced from the pair of characters $(\eta_1,\eta_2)$ is $\eta_1(\det)$ times a polynomial function of the bottom row and its conjugate, the four-variable format being the one used uniformly at real and complex places. It is used in [`AutomorphicForm.exists_sum_mul_localZeta_bottomRow_eq_of_rightTranslatesSpanFinite`](thm.html#AutomorphicForm.exists_sum_mul_localZeta_bottomRow_eq_of_rightTranslatesSpanFinite), where such polynomial expressions feed into the local zeta integrals; the proof invokes the identification of the row-isometry subgroup of $\mathrm{GL}_2(F_w)$ with $\mathrm{O}(2,\mathbb{R})$ entry by entry through $\iota_w$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_mvPolynomial_apply_eq_mul_eval_bottomRow_of_rightTranslatesSpanFinite_of_isReal.lean

import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_BorelSubgroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.WindowedSiegel

theorem AutomorphicForm.exists_mvPolynomial_apply_eq_mul_eval_bottomRow_of_rightTranslatesSpanFinite_of_isReal
    (F : Type) [Field F] (w : InfinitePlace F) (hw : w.IsReal)
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
