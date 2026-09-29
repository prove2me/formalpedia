-- Prove2me | Theorems.Thm_Diaz_four_exp_trdeg_one
-- name    : Diaz.four_exp_trdeg_one
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T09:29:07.546985+00:00
-- url     : https://prove2.me/theorems/6a3a821b-fb9b-4373-b337-2b57cc36fdcf
-- title:
--   Four exponentials in transcendence degree one, from the master dichotomy
-- statement:
--   **Source.** This is the four exponentials theorem in transcendence degree one, which Carlo Perassi states, in unpublished work, as a corollary of the dichotomy below. It **is not his own**: in matrix form it is Theorem 1 of D. Roy and M. Waldschmidt, *Quadratic relations between logarithms of algebraic numbers*, Proc. Japan Acad. Ser. A 71 (1995), 151–153, p. 151, where for its proof they refer to W. D. Brownawell, J. Number Theory 6 (1974), 22–31, and M. Waldschmidt, J. Number Theory 5 (1973), 191–202. It is ported here as an attributed legacy node.
--
--   **Statement.** Let $\lambda_{11},\lambda_{12},\lambda_{21},\lambda_{22}$ be non-zero logarithms of elements of a subfield $K\subset\mathbb C$ (at $K=\overline{\mathbb Q}$, non-zero elements of $\mathcal L$) with
--   $$\lambda_{11}\lambda_{22}=\lambda_{12}\lambda_{21},\qquad \operatorname{trdeg}_{\mathbb Q}\mathbb Q(\lambda_{11},\lambda_{12},\lambda_{21},\lambda_{22})\le 1 .$$
--   Then the two rows, or the two columns, of $\begin{pmatrix}\lambda_{11}&\lambda_{12}\\ \lambda_{21}&\lambda_{22}\end{pmatrix}$ are linearly dependent over $\mathbb Q$. Equivalently, the four exponentials conjecture holds for quadruples of logarithms generating a field of transcendence degree at most one.
--
--   **Provenance of the carried hypothesis.** The dichotomy `hMaster` is Carlo Perassi's master dichotomy for rationally proportional products (unpublished). He derives it from Roy and Waldschmidt's *Théorème 0.2* (D. Roy and M. Waldschmidt, *Approximation diophantienne et indépendance algébrique de logarithmes*, Ann. Sci. École Norm. Sup. (4) 30 (1997), 753–796, p. 755; the dichotomy form), and he records that its $m=1$ case is Exercise 1.8 / the worked example of §12.5 of M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups* (Springer, 2000; pp. 24 and 438–439). The derivation from Théorème 0.2 is not formalised, so the dichotomy is **carried as the explicit hypothesis `hMaster` rather than asserted**: this node asserts only the implication.
--
--   **What the node proves.** Given `hMaster`, the corollary follows by applying the dichotomy to $(\mu_1,\nu_1,\mu_2,\nu_2)=(\lambda_{11},\lambda_{22},\lambda_{12},\lambda_{21})$ with $m=1$. Its third alternative is excluded by the transcendence-degree hypothesis. In the first alternative $\lambda_{12}=c\lambda_{11}$ and $\lambda_{21}=c'\lambda_{22}$, and the product relation forces $cc'=1$, so the second column is $c$ times the first; the second alternative is symmetric and gives the rows. That case analysis, including the derivation of $cc'=1$, is the content actually verified here.
--
--   **Formalization note.** Transcendence degree is `Algebra.trdeg ℚ` of `Algebra.adjoin ℚ` of the four numbers; membership in $\mathcal L$ is `Complex.exp l ∈ K`; "$\mu_2\in\mathbb Q^\times\mu_1$" is `∃ c : ℚ, c ≠ 0 ∧ μ₂ = c * μ₁`; and "linearly dependent over $\mathbb Q$" is the existence of a non-zero rational pair annihilating the two rows, resp. columns. `#print axioms` on the submitted proof: `[propext, Classical.choice, Quot.sound]`.

import Mathlib

open ComplexConjugate

theorem Diaz.four_exp_trdeg_one {K : Subfield ℂ}
    (hMaster : ∀ μ₁ ν₁ μ₂ ν₂ : ℂ,
      Complex.exp μ₁ ∈ K → Complex.exp ν₁ ∈ K → Complex.exp μ₂ ∈ K → Complex.exp ν₂ ∈ K →
      μ₁ ≠ 0 → ν₁ ≠ 0 → μ₂ ≠ 0 → ν₂ ≠ 0 →
      ∀ m : ℚ, m ≠ 0 → μ₂ * ν₂ = (m : ℂ) * (μ₁ * ν₁) →
      ((∃ c : ℚ, c ≠ 0 ∧ μ₂ = (c : ℂ) * μ₁) ∧ (∃ c : ℚ, c ≠ 0 ∧ ν₂ = (c : ℂ) * ν₁))
      ∨ ((∃ c : ℚ, c ≠ 0 ∧ μ₂ = (c : ℂ) * ν₁) ∧ (∃ c : ℚ, c ≠ 0 ∧ ν₂ = (c : ℂ) * μ₁))
      ∨ 2 ≤ Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({μ₁, ν₁, μ₂, ν₂} : Set ℂ)))
    {l₁₁ l₁₂ l₂₁ l₂₂ : ℂ}
    (h₁₁ : Complex.exp l₁₁ ∈ K) (h₁₂ : Complex.exp l₁₂ ∈ K)
    (h₂₁ : Complex.exp l₂₁ ∈ K) (h₂₂ : Complex.exp l₂₂ ∈ K)
    (n₁₁ : l₁₁ ≠ 0) (n₁₂ : l₁₂ ≠ 0) (n₂₁ : l₂₁ ≠ 0) (n₂₂ : l₂₂ ≠ 0)
    (hdet : l₁₁ * l₂₂ = l₁₂ * l₂₁)
    (htd : Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({l₁₁, l₁₂, l₂₁, l₂₂} : Set ℂ)) ≤ 1) :
    (∃ a b : ℚ, ¬(a = 0 ∧ b = 0) ∧
        (a : ℂ) * l₁₁ + (b : ℂ) * l₂₁ = 0 ∧ (a : ℂ) * l₁₂ + (b : ℂ) * l₂₂ = 0)
    ∨ (∃ a b : ℚ, ¬(a = 0 ∧ b = 0) ∧
        (a : ℂ) * l₁₁ + (b : ℂ) * l₁₂ = 0 ∧ (a : ℂ) * l₂₁ + (b : ℂ) * l₂₂ = 0) := by sorry
