-- Prove2me | Theorems.Thm_DistCov_Indep_schoenberg_embedding
-- name    : DistCov.Indep.schoenberg_embedding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:32:10.139082+00:00
-- url     : https://prove2.me/theorems/684b3c1a-1532-43bb-8526-1be7c9e76d40
-- title:
--   p. 9 — Schoenberg: a separable metric space has negative type iff it embeds in ℓ² with d = ‖ϕ − ϕ′‖²
-- statement:
--   Let $(\mathcal X,d)$ be a separable metric space. Recall that $\mathcal X$ has negative type if for all $n$, all $x_1,\dots,x_n\in\mathcal X$ and all real $\alpha_1,\dots,\alpha_n$ with $\sum_i\alpha_i=0$, $\sum_{i,j}\alpha_i\alpha_j d(x_i,x_j)\le0$. Then $\mathcal X$ has negative type if and only if there is a map $\phi:\mathcal X\to\ell^2(\mathbb N)$ such that
--   $$d(x,x')=\|\phi(x)-\phi(x')\|^2\qquad\text{for all }x,x'\in\mathcal X.$$
--
--   This is Schoenberg's theorem (1937, 1938) as quoted in the paper: negative type of $d$ is exactly the existence of an isometric embedding of $(\mathcal X,d^{1/2})$ into a Hilbert space. Such embeddings are the bridge between distance covariance and Hilbert-space geometry used throughout §3.
--
--   **Formalization Note** The paper's Hilbert space $H$ is separable when $\mathcal X$ is (p. 10, "Note that $H$ is separable when $\mathcal X$ is"), and every separable real Hilbert space embeds linearly and isometrically into $\ell^2(\mathbb N)$, so the target is fixed to $\ell^2(\mathbb N)$ (`lp (fun _ : ℕ => ℝ) 2`), indexed from $0$. Separability is the standing assumption of Errata (i), p. 24; the direction from an embedding to (3.1) holds for any Hilbert space, so fixing the target loses nothing there.
-- source:
--   Lyons, Distance covariance in metric spaces, arXiv:1106.5758 (version of 19 Dec. 2020), p. 9, last paragraph (Schoenberg's theorem) and p. 10 ('Note that H is separable when X is'); Errata (i), p. 24

import Mathlib
import Definitions.Def_DistCov_Indep_Setting

namespace DistCov.Indep

open MeasureTheory

theorem schoenberg_embedding {X : Type*} [MetricSpace X] [SecondCountableTopology X] :
    NegType X ↔ ∃ ϕ : X → L2N, IsNegTypeEmbedding ϕ := by sorry

end DistCov.Indep
