-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_norm_tsum_sub_inv_measure_mul_integral_comp_unipotentGL2_le_of_isCompact
-- name    : AutomorphicForm.exists_forall_norm_tsum_sub_inv_measure_mul_integral_comp_unipotentGL2_le_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/b59f3e5f-d33d-5ed6-b974-7d8c1b85ca28
-- title:
--   Uniform Poisson tail bound for unipotent slices of a test function
-- statement:
--   Let $F$ be a number field, with adele ring $\mathbb{A}_F =$ `AdeleRing (𝓞 F) F`, and let $\varphi$ be a complex-valued function on $\mathrm{GL}_2(\mathbb{A}_F)$ that is a factorizable test function: there are $f_\infty$ on $\mathrm{GL}_2$ of the infinite adeles and $f_{\mathrm{fin}}$ on $\mathrm{GL}_2$ of the finite adeles with $\varphi(g) = f_\infty(g_\infty)\, f_{\mathrm{fin}}(g_{\mathrm{fin}})$, where $f_\infty$ has compact support and is of the form $\Phi \circ (\text{matrix entries in the mixed space})$ for some $C^\infty$ function $\Phi$, and $f_{\mathrm{fin}}$ is locally constant with compact support. Let $Q$ be a compact subset of $\mathrm{GL}_2(\mathbb{A}_F) \times \mathrm{GL}_2(\mathbb{A}_F)$ and let $N$ be a natural number. Then there is a real constant $C$ such that for every $p = (p_1,p_2) \in Q$, every unit $a$ of $\mathbb{A}_F$ whose finite component equals $1$ and whose infinite component has $\|a_w\| = t$ at every infinite place $w$ for some real $t \ge 1$, and every adele $e$, the quantity $$\Bigl\| \sum_{\beta \in F} \varphi\bigl(p_1\, n((\beta + e)a^{-1})\, p_2\bigr) - \mu(\mathcal{B})^{-1} \int_{\mathbb{A}_F} \varphi\bigl(p_1\, n((u+e)a^{-1})\, p_2\bigr)\, d\mu(u) \Bigr\|$$ is at most $C\, (t^{-1})^{N}$. Here $n(x)$ is the unipotent matrix $\begin{pmatrix} 1 & x \\ 0 & 1\end{pmatrix}$, $\mu$ is the additive Haar measure `adelicAddHaar` on $\mathbb{A}_F$ for its Borel structure, $\mathcal{B}$ is the adelic box consisting of the adeles whose infinite part lies in the fundamental domain of the lattice basis of the mixed space and whose finite part is integral at every finite place, and $\mu(\mathcal{B})^{-1}$ denotes the inverse of the real number $\mu(\mathcal{B})$ viewed in $\mathbb{C}$.
--
--   This is the uniform Poisson-summation estimate for the unipotent slices of a test function on $\mathrm{GL}_2(\mathbb{A}_F)$: along a compact family of left and right translates, and for arbitrary adelic shifts, the lattice sum over $F$ differs from the correspondingly normalised adelic integral by $O(t^{-N})$ in the dilation parameter $t$, with one constant for the whole family. It feeds the bounds comparing the Borel part of the automorphic kernel of $\varphi$ with its constant term in terms of inverse powers of the adelic height, used in the analysis of the unipotent contribution to the trace formula.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_norm_tsum_sub_inv_measure_mul_integral_comp_unipotentGL2_le_of_isCompact.lean

import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox

theorem AutomorphicForm.exists_forall_norm_tsum_sub_inv_measure_mul_integral_comp_unipotentGL2_le_of_isCompact
    (F : Type) [Field F] [NumberField F]
    (φ : Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 F) F) → ℂ)
    (hφ : AutomorphicForm.IsFactorizableTestFn F φ)
    (Q : Set (Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 F) F) ×
      Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 F) F))) (hQ : IsCompact Q) (N : ℕ) :
    ∃ C : ℝ, ∀ p ∈ Q, ∀ (a : (AdeleRing (𝓞 F) F)ˣ) (t : ℝ), 1 ≤ t → (a : AdeleRing (𝓞 F) F).2 = 1 →
      (∀ w : InfinitePlace F, ‖(a : AdeleRing (𝓞 F) F).1 w‖ = t) → ∀ e : AdeleRing (𝓞 F) F,
        ‖(∑' β : F, φ (p.1 * AutomorphicForm.unipotentGL2
              ((algebraMap F (AdeleRing (𝓞 F) F) β + e) * ↑a⁻¹) * p.2)) -
            ((adelicAddHaar (𝓞 F) F (adelicBox F)).toReal : ℂ)⁻¹ *
              ∫ u, φ (p.1 * AutomorphicForm.unipotentGL2 ((u + e) * ↑a⁻¹) * p.2) ∂(adelicAddHaar (𝓞 F) F)‖
          ≤ C * t⁻¹ ^ N := by sorry
