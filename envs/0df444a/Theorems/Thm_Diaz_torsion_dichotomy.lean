-- Prove2me | Theorems.Thm_Diaz_torsion_dichotomy
-- name    : Diaz.torsion_dichotomy
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T07:05:22.688977+00:00
-- url     : https://prove2.me/theorems/c22fae75-ce4c-478a-b100-bb0aafdbd1ee
-- title:
--   Torsion dichotomy: some power of $e^{u}$ is positive real exactly when $\Im u \in \pi\mathbb{Q}$
-- statement:
--   **Source.** This is Carlo Perassi's mathematics, the equivalence (ii) <-> (iii) of his torsion dichotomy, unpublished apart from this node. Published on his mission with his permission. No novelty is claimed for it here; the argument is elementary.
--
--   **Statement.** For $u \in \mathbb{C}$ and $\alpha = e^{u}$, write $\theta = \Im u$. Then
--   $$\theta \in \pi\mathbb{Q} \iff \alpha^{k} \in \mathbb{R}_{>0} \text{ for some } k \geq 1 .$$
--
--   **Context.** The dichotomy has four equivalent clauses: (i) $\alpha/|\alpha|$ is a root of unity; (ii) $\theta \in \pi\mathbb{Q}$; (iii) $\alpha^{k} \in \mathbb{R}_{>0}$ for some $k \geq 1$; (iv) $qu$ has real exponential for some $q \in \mathbb{Q}^\times$. Clauses (i) and (iv) are restatements of (ii) that need no further exponential input; (ii) $\leftrightarrow$ (iii) is the part carrying the arithmetic of $\ker\exp$, and it is what is recorded here. Together with the axis lemma it splits the Diaz locus into a *torsion branch*, which collapses to the single relation $(\log b)^2 + \pi^2 \in \overline{\mathbb{Q}}$, and a non-torsion branch that a two-dimensional Laurent model cannot express.
--
--   **Proof.** $\alpha^{k} = e^{ku}$, and $e^{ku}$ is a positive real exactly when $e^{i k \theta} = 1$, i.e. $k\theta \in 2\pi\mathbb{Z}$. If $\theta = q\pi$ with $q = p/d$, take $k = 2d$: then $k\theta = 2p\pi$ and $e^{ku} = e^{k \Re u} > 0$. Conversely, if $e^{ku}$ is real then its imaginary part $e^{k\Re u}\sin(k\theta)$ vanishes, so $k\theta = n\pi$ and $\theta = (n/k)\pi \in \pi\mathbb{Q}$.

import Mathlib

open ComplexConjugate

theorem Diaz.torsion_dichotomy (u : ℂ) :
    (∃ q : ℚ, u.im = (q : ℝ) * Real.pi) ↔
      ∃ k : ℕ, 0 < k ∧ ∃ t : ℝ, 0 < t ∧ Complex.exp u ^ k = (t : ℂ) := by sorry
