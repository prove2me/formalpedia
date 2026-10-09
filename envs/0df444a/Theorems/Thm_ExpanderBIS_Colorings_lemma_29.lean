-- Prove2me | Theorems.Thm_ExpanderBIS_Colorings_lemma_29
-- name    : ExpanderBIS.Colorings.lemma_29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:32:18.77795+00:00
-- url     : https://prove2.me/theorems/ee9b1f94-acd8-4e21-89ec-a9b251e5809e
-- title:
--   Lemma 29 — for Δ ≥ Cq² log² q, Z̃_G(q) = Σ_{(A,B)} |A|^m|B|^m Ξ_{A,B}(G) is an e^{−m/(4q)}-relative approximation to Z_G(q)
-- statement:
--   There is an absolute constant $C$ such that the following holds. Let $q \ge 3$, let $\Delta \ge Cq^2\log^2 q$, let $m \ge 1$, and let $G$ be a $\Delta$-regular bipartite graph with sides of size $m$ that is a $\bigl(\frac{4\log\Delta}{\Delta}, \frac{\Delta}{4\log\Delta} - \frac12\bigr)$-expander. Then
--   $$\tilde Z_G(q) = \sum_{(A,B) \in \mathcal P} |A|^m|B|^m\, \Xi_{A,B}(G)$$
--   is an $e^{-m/(4q)}$-relative approximation to the number $Z_G(q)$ of proper $q$-colorings of $G$:
--   $$e^{-\varepsilon}\tilde Z_G(q) \le Z_G(q) \le e^{\varepsilon}\tilde Z_G(q), \qquad \varepsilon = e^{-m/(4q)}.$$
--
--   This is the reduction half of Theorem 5: counting proper colorings is reduced, up to an exponentially small relative error, to $2^q$ polymer partition functions.
--
--   **Formalization Note.** The paper writes $e^{-m/4q}$, read as $e^{-m/(4q)}$ (p. 31 uses $\varepsilon > e^{-n/(8q)}$ with $n = 2m$). The hypothesis $m \ge 1$ is added: on the empty vertex set ($m = 0$) the edgeless graph is vacuously $\Delta$-regular, $Z_G(q) = 1$ while $\tilde Z_G(q) = 2^q$, and the statement fails. $C$ is quantified before $q$, $\Delta$, $m$ and $G$, so it is absolute.
-- source:
--   Jenssen, Keevash and Perkins, Algorithms for #BIS-hard problems on expander graphs, SIAM J. Comput. 49(4) (2020), author accepted manuscript, p. 27, Lemma 29 (proof pp. 27–30)

import Mathlib
import Definitions.Def_ExpanderBIS_Colorings_Setting

open Classical Finset

namespace ExpanderBIS.Colorings

theorem lemma_29 :
    ∃ C : ℝ, ∀ q : ℕ, 3 ≤ q → ∀ Δ : ℕ, C * (q : ℝ) ^ 2 * Real.log q ^ 2 ≤ Δ →
      ∀ m : ℕ, 0 < m → ∀ G ∈ ExpanderBIS.RandomHardCore.Gbip m Δ, ExpanderBIS.RandomHardCore.IsStdExpander G Δ →
        ExpanderBIS.Potts.IsRelApprox (Real.exp (-((m : ℝ) / (4 * q)))) (Ztilde G q Δ)
          ((properColorings G q).card) := by sorry

end ExpanderBIS.Colorings
