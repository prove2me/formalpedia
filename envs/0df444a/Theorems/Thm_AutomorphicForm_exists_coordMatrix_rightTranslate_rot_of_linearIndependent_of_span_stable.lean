-- Prove2me | Theorems.Thm_AutomorphicForm_exists_coordMatrix_rightTranslate_rot_of_linearIndependent_of_span_stable
-- name    : AutomorphicForm.exists_coordMatrix_rightTranslate_rot_of_linearIndependent_of_span_stable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/1fd435a0-d86a-5960-bccc-41e3a8694fdc
-- title:
--   Coordinate matrices for an SU(2)-string at a complex place
-- statement:
--   Let $F$ be a number field, $w$ a complex infinite place of $F$, and $n$ a natural number. For a $2\times 2$ complex matrix $e$ write $e_w$ for the element of $\mathrm{GL}_2(\mathbb{A}_F)$ obtained by placing $e$ at the $w$-component through the identification of the completion at $w$ with $\mathbb{C}$ (and $1$ if $\det e = 0$), as in `archComplexLiftAt`; put $R(s) = \bigl(\begin{smallmatrix}\cos s & -\sin s\\ \sin s & \cos s\end{smallmatrix}\bigr)_w$ and $S(s) = \bigl(\begin{smallmatrix}\cos s & i\sin s\\ i\sin s & \cos s\end{smallmatrix}\bigr)_w$ for $s \in \mathbb{R}$. Let $x_0,\dots,x_n : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be linearly independent over $\mathbb{C}$, and assume: for all $p$ and all $s$, the functions $g \mapsto x_p(g R(s))$ and $g \mapsto x_p(g S(s))$ lie in the $\mathbb{C}$-span of $\{x_0,\dots,x_n\}$; and for all $p$ and all $g$, the functions $s \mapsto x_p(gR(s))$ and $s \mapsto x_p(gS(s))$ have derivatives at $s=0$ equal to $\sum_{p'} (M_1)_{p'p} x_{p'}(g)$ and $\sum_{p'} (M_2)_{p'p} x_{p'}(g)$, where $(M_1)_{p'p} = 1$ if $p' = p+1$, $-p(n+1-p)$ if $p = p'+1$, $0$ otherwise, and $(M_2)_{p'p} = i$ if $p' = p+1$, $i\,p(n+1-p)$ if $p = p'+1$, $0$ otherwise (indices compared as natural numbers). Then there exist $E_1, E_2 : \mathbb{R} \to M_{n+1}(\mathbb{C})$ with $E_1(0) = E_2(0) = 1$, with each entry $s \mapsto E_k(s)_{ij}$ differentiable at $0$ with derivative $(M_k)_{ij}$, and with $x_p(gR(s)) = \sum_{p'} E_1(s)_{p'p} x_{p'}(g)$ and $x_p(gS(s)) = \sum_{p'} E_2(s)_{p'p} x_{p'}(g)$ for all $p$, $s$ and $g$.
--
--   This packages the translation action of the two compact one-parameter subgroups at a complex place on a linearly independent, translation-stable family of functions into matrix coefficients $E_1, E_2$ normalised at $s = 0$ with prescribed derivative there, the ladder matrices of an unnormalised $\mathfrak{sl}_2$-string. It is used in [`AutomorphicForm.CuspidalConstituent.exists_eq_sum_su2String_highestWeight_of_mem_cut_of_isComplex`](thm.html#AutomorphicForm.CuspidalConstituent.exists_eq_sum_su2String_highestWeight_of_mem_cut_of_isComplex), where the $K$-type of a cuspidal constituent at a complex place is analysed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_coordMatrix_rightTranslate_rot_of_linearIndependent_of_span_stable.lean

import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem AutomorphicForm.exists_coordMatrix_rightTranslate_rot_of_linearIndependent_of_span_stable
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)
    (n : ℕ) (x : Fin (n + 1) → (AdelicGL2 (𝓞 F) F → ℂ)) (hli : LinearIndependent ℂ x)
    (hR : ∀ (p : Fin (n + 1)) (s : ℝ),
      (fun g => x p (g * archComplexLiftAt hw
        !![(Real.cos s : ℂ), -(Real.sin s : ℂ); (Real.sin s : ℂ), (Real.cos s : ℂ)])) ∈ Submodule.span ℂ (Set.range x))
    (hS : ∀ (p : Fin (n + 1)) (s : ℝ),
      (fun g => x p (g * archComplexLiftAt hw
        !![(Real.cos s : ℂ), (Real.sin s : ℂ) * Complex.I; (Real.sin s : ℂ) * Complex.I, (Real.cos s : ℂ)])) ∈
          Submodule.span ℂ (Set.range x))
    (hR' : ∀ (p : Fin (n + 1)) (g : AdelicGL2 (𝓞 F) F),
      HasDerivAt (fun s : ℝ => x p (g * archComplexLiftAt hw
        !![(Real.cos s : ℂ), -(Real.sin s : ℂ); (Real.sin s : ℂ), (Real.cos s : ℂ)]))
        (∑ p' : Fin (n + 1),
          (if (p' : ℕ) = p + 1 then 1 else if (p : ℕ) = p' + 1 then -((p : ℂ) * ((n : ℂ) + 1 - p)) else 0) * x p' g) 0)
    (hS' : ∀ (p : Fin (n + 1)) (g : AdelicGL2 (𝓞 F) F),
      HasDerivAt (fun s : ℝ => x p (g * archComplexLiftAt hw
        !![(Real.cos s : ℂ), (Real.sin s : ℂ) * Complex.I; (Real.sin s : ℂ) * Complex.I, (Real.cos s : ℂ)]))
        (∑ p' : Fin (n + 1),
          (if (p' : ℕ) = p + 1 then Complex.I else if (p : ℕ) = p' + 1 then Complex.I * ((p : ℂ) * ((n : ℂ) + 1 - p)) else 0) *
            x p' g) 0) :
    ∃ E₁ E₂ : ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      E₁ 0 = 1 ∧ E₂ 0 = 1 ∧
      (∀ i j : Fin (n + 1), HasDerivAt (fun s : ℝ => E₁ s i j)
        (if (i : ℕ) = j + 1 then 1 else if (j : ℕ) = i + 1 then -((j : ℂ) * ((n : ℂ) + 1 - j)) else 0) 0) ∧
      (∀ i j : Fin (n + 1), HasDerivAt (fun s : ℝ => E₂ s i j)
        (if (i : ℕ) = j + 1 then Complex.I else if (j : ℕ) = i + 1 then Complex.I * ((j : ℂ) * ((n : ℂ) + 1 - j)) else 0) 0) ∧
      (∀ (p : Fin (n + 1)) (s : ℝ) (g : AdelicGL2 (𝓞 F) F),
        x p (g * archComplexLiftAt hw !![(Real.cos s : ℂ), -(Real.sin s : ℂ); (Real.sin s : ℂ), (Real.cos s : ℂ)]) =
          ∑ p' : Fin (n + 1), E₁ s p' p * x p' g) ∧
      (∀ (p : Fin (n + 1)) (s : ℝ) (g : AdelicGL2 (𝓞 F) F),
        x p (g * archComplexLiftAt hw
          !![(Real.cos s : ℂ), (Real.sin s : ℂ) * Complex.I; (Real.sin s : ℂ) * Complex.I, (Real.cos s : ℂ)]) =
          ∑ p' : Fin (n + 1), E₂ s p' p * x p' g) := by sorry
