-- Prove2me | Theorems.Thm_DihedralWeightOne_sum_weightOneLift_mul_padicToAdelic_inv_eq_mul_slash_apply_I_mul_det
-- name    : DihedralWeightOne.sum_weightOneLift_mul_padicToAdelic_inv_eq_mul_slash_apply_I_mul_det
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/44435287-6108-5446-8aa9-6d90e32e5d5d
-- title:
--   Hecke coset sum for the weight-one adelic lift at a good prime
-- statement:
--   Fix $N\ge 1$, a Dirichlet character $\varepsilon$ modulo $N$ with values in $\mathbb{C}$, and a cusp form $F$ of weight $1$ for $\Gamma_1(N)$ satisfying [`CuspForm.HasNebentypus`](def/CuspForm_PrimitiveFormGamma1.html#L13) $\varepsilon$, i.e. $F(\gamma\cdot\tau)=\varepsilon(\gamma_{11}\bmod N)\,(\gamma_{10}\tau+\gamma_{11})\,F(\tau)$ for all $\gamma\in\Gamma_0(N)\subseteq\mathrm{SL}_2(\mathbb{Z})$ and all $\tau$ in the upper half-plane. Let $p$ be a prime with $p\nmid N$, and let $\rho_0,\dots,\rho_p\in\mathrm{GL}_2(\mathbb{Q}_p)$ have underlying matrices $\begin{pmatrix}1&i\\0&p\end{pmatrix}$ for $i<p$ and $\begin{pmatrix}p&0\\0&1\end{pmatrix}$ for $i=p$. Let $h\in\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ be such that its image `glFin` in $\mathrm{GL}_2$ of the finite adeles is the identity, and such that the real matrix $h_\infty=$ [`LanglandsTunnell.ratArchGL2`](def/LanglandsTunnell_DeltaLift.html#L16) $h$, obtained from the archimedean component of $h$ at the default infinite place of $\mathbb{Q}$, has positive determinant. Then the sum over $i\in\{0,\dots,p\}$ of `weightOneLift` at level $N\mathcal{O}_{\mathbb{Q}}$ of $F$, evaluated at $h\cdot$ [`AdelicDock.padicToAdelic`](def/AdelicDock_LocalEmbedding.html#L254) $p\,\rho_i^{-1}$ (the embedding of $\mathrm{GL}_2(\mathbb{Q}_p)$ into $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ at the place above $p$), equals $$p\cdot\Bigl(\bigl(\varepsilon(p)^{-1}\cdot U_pF+F\mid_1\mathrm{diag}(p,1)\bigr)\Big|_1 h_\infty\Bigr)(i)\cdot\det h_\infty,$$ where $U_pF=\sum_{j<p}F\mid_1\begin{pmatrix}1&j\\0&p\end{pmatrix}$ is [`ModularForm.heckeU`](def/ModularForm_HeckeOperator.html#L93) $1\,p$, all slash actions are in weight $1$, and $\det h_\infty$ is cast from $\mathbb{R}$ to $\mathbb{C}$. Here `weightOneLift` $N\mathcal{O}_{\mathbb{Q}}$ $f$ $g$ is, when $g$ admits a decomposition $g=\gamma\, h' u$ with $\gamma$ rational, $u$ in the level-$N$ compact subgroup, `glFin` $h'=1$ and $\det h'_\infty>0$, the value $(f\mid_1 h'_\infty)(i)\cdot(\det h'_\infty)^1$ for a chosen such witness, and $0$ otherwise.
--
--   This is the weight-one counterpart of the computation of the adelic Hecke coset sum at a prime not dividing the level: the $p+1$ cosets $\rho_i$ of the local Hecke operator, applied on the right to a finite-trivial adelic point, give back the classical operator $\varepsilon(p)^{-1}U_p+\mid_1\mathrm{diag}(p,1)$ read through the archimedean slash action, with an extra factor $p$ coming from the determinant weight of the weight-one lift. It feeds the identification of the adelic Hecke eigenvalues of the lift with the $q$-expansion coefficients of $F$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DihedralWeightOne_sum_weightOneLift_mul_padicToAdelic_inv_eq_mul_slash_apply_I_mul_det.lean

import Mathlib
import Definitions.Def_AutomorphicForm_DihedralWeightOneLift
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm DihedralWeightOne IsDedekindDomain
open scoped MatrixGroups ModularForm

theorem DihedralWeightOne.sum_weightOneLift_mul_padicToAdelic_inv_eq_mul_slash_apply_I_mul_det
    {N : ℕ} [NeZero N] {ε : DirichletCharacter ℂ N} {F : CuspForm (CongruenceSubgroup.Gamma1 N) 1}
    (hε : CuspForm.HasNebentypus ε F)
    (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (ρ : Fin (p + 1) → GL (Fin 2) ℚ_[p])
    (hρ : ∀ i : Fin (p + 1), ((ρ i : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) =
      if (i : ℕ) < p then !![(1 : ℚ_[p]), ((i : ℕ) : ℚ_[p]); 0, (p : ℚ_[p])]
      else !![(p : ℚ_[p]), 0; 0, 1])
    {h : AdelicGL2 (𝓞 ℚ) ℚ}
    (hh : glFin (𝓞 ℚ) ℚ h = 1)
    (hpos : LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ) :
    ∑ i : Fin (p + 1), weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑F) (h * AdelicDock.padicToAdelic p (ρ i)⁻¹) =
      (p : ℂ) *
        ((((ε (p : ZMod N))⁻¹ • ModularForm.heckeU 1 p ⇑F +
              (⇑F) ∣[(1 : ℤ)] ModularForm.heckeDiagMatrix p) ∣[(1 : ℤ)]
            LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I *
          (((LanglandsTunnell.ratArchGL2 h).det.val : ℝ) : ℂ)) := by sorry
