-- Prove2me | Theorems.Thm_DiazModulus_candidate_multiplier_module
-- name    : DiazModulus.candidate_multiplier_module
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-12T09:16:04.218351+00:00
-- url     : https://prove2.me/theorems/69387a9d-5e97-4b55-b6e6-64fa30ba558f
-- title:
--   A candidate's multiplier module is exactly $\overline{\mathbb{Q}} + \overline{\mathbb{Q}}u^{-1}$
-- statement:
--   **The multiplier module of a hypothetical counterexample is exactly $\overline{\mathbb{Q}} + \overline{\mathbb{Q}}\,u^{-1}$.**
--
--   Write $\overline{\mathbb{Q}}$ for the algebraic numbers, $\mathcal{L} = \{z : e^{z} \in \overline{\mathbb{Q}}\}$, and $\widetilde{\mathcal{L}}$ for the $\overline{\mathbb{Q}}$-span of $\{1\} \cup \mathcal{L}$. Following the mission's convention, a **candidate** is a $u$ with $u \neq 0$, $|u|$ algebraic and $e^{u}$ algebraic — exactly a counterexample to Diaz's modulus conjecture.
--
--   Assume Roy's **strong six exponentials theorem**, carried here as the hypothesis `hSSE`: for $\overline{\mathbb{Q}}$-linearly independent $x_1,x_2$ and $\overline{\mathbb{Q}}$-linearly independent $y_1,y_2,y_3$, at least one of the six products $x_i y_j$ lies outside $\widetilde{\mathcal{L}}$. Assume also Hermite--Lindemann. Then for every candidate $u$:
--
--   1. $\{z \in \widetilde{\mathcal{L}} : uz \in \widetilde{\mathcal{L}}\} = \overline{\mathbb{Q}} + \overline{\mathbb{Q}}\,u^{-1}$;
--   2. $u^{2} \notin \widetilde{\mathcal{L}}$;
--   3. $(u-a)^{-1} \notin \widetilde{\mathcal{L}}$ for every non-zero algebraic $a$.
--
--   **Proof.** Both $u$ and $u^{-1} = \bar u / |u|^{2}$ lie in $\widetilde{\mathcal{L}}$, and for $z = a + b/u$ with $a,b$ algebraic one has $uz = au + b$; that is the inclusion $\supseteq$ in (1). Conversely suppose $z \in \widetilde{\mathcal{L}}$, $uz \in \widetilde{\mathcal{L}}$, and $z \notin \overline{\mathbb{Q}} + \overline{\mathbb{Q}}u^{-1}$. By Hermite--Lindemann $u$ is transcendental, so $1,u$ are $\overline{\mathbb{Q}}$-linearly independent and so are $1,u^{-1}$; adjoining $z$ keeps independence, by the assumption on $z$. All six products of $(1,u)$ with $(z,1,u^{-1})$ — namely $z,\,1,\,u^{-1},\,uz,\,u,\,1$ — then lie in $\widetilde{\mathcal{L}}$, contradicting `hSSE`.
--
--   Clause (2) is (1) at $z = u$: it would give $u = a + b/u$, making $u$ a root of $X^{2} - aX - b$ over $\overline{\mathbb{Q}}$, hence algebraic. Clause (3) is (1) at $z = (u-a)^{-1}$, legitimate because $uz = 1 + az \in \widetilde{\mathcal{L}}$; the conclusion of (1) again forces a non-trivial quadratic relation for $u$ over $\overline{\mathbb{Q}}$, the case of a vanishing leading coefficient being excluded by $a \neq 0$.
--
--   **Attribution.** Clause (1) is the case $x = (1, u)$, $y = (z, u^{-1})$ of Théorème 4(1) of G. Diaz, *Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques*, J. Théor. Nombres Bordeaux **19** (2007), p. 385, and the case $\Lambda_{1} = u$ of Corollary 2.2 of M. Waldschmidt, *Variations on the six exponentials theorem* (2005). Clause (2) is Corollaire 5(1) of Diaz 2007 (p. 383), since $u/\bar u = u^{2}/|u|^{2}$; see also Théorème 3(1) of Diaz, J. Théor. Nombres Bordeaux **16** (2004). Clause (3) is Corollaire 5(4) of Diaz 2007. The same Corollaire 5, point (2), gives $u^{3} \notin \widetilde{\mathcal{L}}$ as well.
--
--   **Why it matters.** It is already recorded here that no six-exponentials template can be assembled inside the three-dimensional hull $\operatorname{span}_{\overline{\mathbb{Q}}}\{1,u,\bar u\}$ that a candidate certifies out of itself. This is the complementary statement: it says exactly what a third multiplier would have to be, and that no algebraic operation on $u$ supplies one. Two consequences at the level of values: $e^{\beta u^{2}}$ is transcendental for every non-zero algebraic $\beta$, and $e^{b/(u-a)}$ is transcendental for all non-zero algebraic $a,b$ — while $1/u$ itself necessarily remains in $\widetilde{\mathcal{L}}$.
-- source:
--   Roy's strong six exponentials theorem (D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47), carried as an explicit hypothesis. The three clauses are cases of G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391, Théorème 4(1) and Corollaire 5(1), 5(4), and of M. Waldschmidt, Variations on the six exponentials theorem, in Algebra and Number Theory (R. Tandon, ed.), Hindustan Book Agency, 2005, Corollary 2.2. Formal proof: Diaz modulus mission, 12 September 2026 (C. Perassi).

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus
theorem candidate_multiplier_module
    (hSSE : ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
      LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ (∀ i j, x i * y j ∈ LogAlgTilde))
    (hHL : HermiteLindemann) {u : ℂ} (h : IsCandidate u) :
    {z : ℂ | z ∈ LogAlgTilde ∧ u * z ∈ LogAlgTilde}
        = (Submodule.span Qbar ({1, u⁻¹} : Set ℂ) : Set ℂ)
      ∧ u ^ 2 ∉ LogAlgTilde
      ∧ ∀ a : ℂ, a ∈ Qbar → a ≠ 0 → (u - a)⁻¹ ∉ LogAlgTilde := by sorry
end DiazModulus
