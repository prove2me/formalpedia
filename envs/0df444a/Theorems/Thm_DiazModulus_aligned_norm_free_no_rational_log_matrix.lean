-- Prove2me | Theorems.Thm_DiazModulus_aligned_norm_free_no_rational_log_matrix
-- name    : DiazModulus.aligned_norm_free_no_rational_log_matrix
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T15:54:47.953152+00:00
-- url     : https://prove2.me/theorems/931b8b88-3036-4006-9045-de1f1ebd4ecf
-- title:
--   Period-aligned, norm-free: no four-exponentials matrix over the certified logarithm span
-- statement:
--   **On the period-aligned, norm-free half, the four exponentials statement has no matrix to act on — and this is a theorem, not a gap in the search.**
--
--   **Setting.** Let $u\in\mathbb C$ with $t=\Re u\neq0$, and let $r\in\mathbb Q$ be an aligned witness: $\beta:=\pi(\Im u+r\pi)$ is a non-zero algebraic number. Let $A:=\lVert u\rVert^{2}$ be algebraic. The hypothesis of this statement is the **norm-free** one, $A\notin\mathbb Q\cdot\beta$; it is the complement of the half `DiazModulus.diaz_of_exp_not_real_irrational_angle_period_aligned_norm_rat_mult`, where $A=c\beta$ with $c\in\mathbb Q$ and the four exponentials statement does apply.
--
--   Under a counterexample ($e^{u}$ algebraic) the logarithms of algebraic numbers that the class data certifies are exactly the $\mathbb Q$-span
--   $$L_3=\operatorname{span}_{\mathbb Q}\{\,u,\ \bar u,\ 2\pi i\,\},$$
--   which already contains $\Re u=\log|e^{u}|$, the second fibre point $u+2\pi i r$, and the aligned carrier $\nu=i(\Im u+r\pi)$.
--
--   **Statement.** Every $2\times2$ matrix with entries in $L_3$ and vanishing determinant has $\mathbb Q$-linearly dependent rows or $\mathbb Q$-linearly dependent columns. Consequently the hypothesis package of the four exponentials statement — four entries in $\mathcal L$, determinant zero, rows and columns $\mathbb Q$-independent — is **unsatisfiable** over the certified span on this half.
--
--   **Why.** Write $x=\pi i$. Since $\Im u=\beta/\pi-r\pi$, a general element of $L_3$ is
--   $$\lambda=p\,t+q\,\tfrac{\beta}{x}+s\,x,\qquad p,q,s\in\mathbb Q,$$
--   the change of variables from $(a,b,c)$ in $au+b\bar u+c\,2\pi i$ being a $\mathbb Q$-linear bijection. Expanding $\det$ in this basis and using the aligned quartic relation $t^{2}\pi^{2}+r^{2}\pi^{4}-(A+2r\beta)\pi^{2}+\beta^{2}=0$, the imaginary part of $\det=0$ gives $\beta G+\pi^{2}H=0$, forcing $G=H=0$ because $\pi^{2}$ is transcendental and $\beta$ is algebraic; the real part becomes an algebraic quadratic relation in $\pi^{2}$, whose three coefficients must vanish, and the middle one reads
--   $$P\,A+\bigl(2rP+J\bigr)\beta=0,\qquad P,J\in\mathbb Q .$$
--   On the sibling half this is solvable with $P\neq0$; here $A/\beta\notin\mathbb Q$ forces $P=0$, and then all six determinant-and-polarisation forms $P,Q,S,G,H,J$ of the three rational coefficient matrices vanish. So the quadratic form $\det$ vanishes identically on the rational subspace they span, every element of that subspace has rank $\le1$, and a common kernel vector or a common image line — rational, by construction — yields the dependence.
--
--   **Scope, stated honestly.** The obstruction is $\mathbb Q$-linear, so clearing denominators cannot help: making $\det$ vanish would require an entry $c\cdot2\pi i$ with $c$ algebraic irrational, and then $\exp(c\cdot 2\pi i)$ is transcendental by Gelfond–Schneider, so that entry is not a logarithm of an algebraic number. The same computation applied to every $2\times2$ minor extends the conclusion to $d\times l$ matrices of rank $\le1$; in particular the **six exponentials theorem** (the case $dl>d+l$, where the rank statement is proved) is equally inapplicable here. The claim is exactly as strong as its span: it says nothing about $\overline{\mathbb Q}$-coefficient combinations, which are the *strong* four exponentials conjecture, nor about routes that do not go through a matrix of logarithms.
--
--   **Relation to the board.** The rank-one classification used at the end is `Diaz.rational_singular_subspace_classification` in greater generality. `DiazModulus.sixExponentials_cannot_refute_candidate` is a no-go of the same shape over $\operatorname{span}_{\overline{\mathbb Q}}\{1,u,\bar u\}$; this one is over the $\mathbb Q$-span containing $2\pi i$, which is what the exponentials statements accept as entries, and it rules out the $2\times2$ template that the other one still permits.
--
--   **Correction to the record.** The description of `DiazModulus.diaz_of_exp_not_real_irrational_angle_period_aligned_norm_free` sketches this conclusion by expanding in the monomials $1,t^{2},t/\pi,t\pi,\pi^{2}$ and assuming they are $\mathbb Q$-linearly independent. That assumption is false on the aligned class — the quartic relation above is exactly a dependence among them, and it is what puts the class in transcendence degree one. The conclusion survives; the argument above replaces the one given there and needs only the transcendence of $\pi$, $\Re u\neq0$ and $\beta\neq0$.
--
--   **Status.** `Transcendental ℚ π` is carried as an explicit hypothesis because it is not in Mathlib at this revision. No proof is claimed here beyond what the statement asserts; nothing is asserted about whether the parent leaf is true.

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus
theorem aligned_norm_free_no_rational_log_matrix :
    ∀ (u : ℂ) (r : ℚ),
      Transcendental ℚ ((Real.pi : ℝ) : ℂ) →
      u.re ≠ 0 →
      Real.pi * (u.im + (r : ℝ) * Real.pi) ≠ 0 →
      IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ) →
      IsAlgebraic ℚ ((((‖u‖ : ℝ)) ^ 2 : ℝ) : ℂ) →
      (¬ ∃ c : ℚ, (‖u‖ : ℝ) ^ 2 = (c : ℝ) * (Real.pi * (u.im + (r : ℝ) * Real.pi))) →
      ∀ l : Fin 2 → Fin 2 → ℂ,
        (∀ i j, ∃ a b c : ℚ, l i j = (a : ℂ) * u + (b : ℂ) * (starRingEnd ℂ) u
          + (c : ℂ) * (2 * ((Real.pi : ℝ) : ℂ) * Complex.I)) →
        l 0 0 * l 1 1 - l 0 1 * l 1 0 = 0 →
        (∃ a b : ℚ, (a ≠ 0 ∨ b ≠ 0) ∧
            (a : ℂ) * l 0 0 + (b : ℂ) * l 1 0 = 0 ∧
            (a : ℂ) * l 0 1 + (b : ℂ) * l 1 1 = 0)
      ∨ (∃ a b : ℚ, (a ≠ 0 ∨ b ≠ 0) ∧
            (a : ℂ) * l 0 0 + (b : ℂ) * l 0 1 = 0 ∧
            (a : ℂ) * l 1 0 + (b : ℂ) * l 1 1 = 0) := by sorry
end DiazModulus
