-- Prove2me | Theorems.Thm_AggGameNet_Sync_lemma_1
-- name    : AggGameNet.Sync.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:37:12.815293+00:00
-- url     : https://prove2.me/theorems/28f43863-4a3e-4391-87d9-3779ca86c2fa
-- title:
--   Lemma 1, p. 9 — geometric mixing of time-varying weights
-- statement:
--   Let $N\ge1$. If each union of $Q\ge1$ consecutive communication graphs is connected, and the matrices $W(k)$ have unit row and column sums with weights at least $\delta>0$ on self-neighbours and graph edges and zero elsewhere, write $\Phi(k,s)=W(k)\cdots W(s)$. For every fixed $s\ge0$,
--
--   $$\Phi(k,s)\longrightarrow\frac1N\mathbf1\mathbf1^\top,$$
--
--   and for all $k\ge s$ and entries $i,j$,
--
--   $$\left|[\Phi(k,s)]_{ij}-\frac1N\right|\le\theta\beta^{k-s},\quad\theta=\left(1-\frac{\delta}{4N^2}\right)^{-2},\quad\beta=\left(1-\frac{\delta}{4N^2}\right)^{1/Q}.$$
--
--   The entrywise estimate controls the error between local and global aggregate estimates. Lean writes $k=s+m$ and takes the limit as $m\to\infty$.
--
--   **Formalization Note** The positive lower bound $\delta>0$ is implicit in the paper's mixing claim and made explicit here.
-- source:
--   Koshal, Nedić, Shanbhag, Distributed Algorithms for Aggregative Games on Graphs, arXiv:1605.00267v2, Lemma 1, p. 9

import Mathlib
import Definitions.Def_AggGameNet_Sync_Setting

namespace AggGameNet.Sync

open Filter
open scoped Topology

/-- Lemma 1, p. 9: geometric mixing of the time-varying matrix products. -/
theorem lemma_1 {N : ℕ} (hN : 0 < N)
    (G : ℕ → SimpleGraph (Fin N)) (Q : ℕ) (h4 : Assumption4 G Q)
    (W : ℕ → Matrix (Fin N) (Fin N) ℝ) (δ : ℝ)
    (hδ : 0 < δ) (h5 : Assumption5 G W δ) :
    (∀ s, Tendsto (fun m => Phi W s m) atTop
      (𝓝 (Matrix.of (fun _ _ => (1 / (N : ℝ)))))) ∧
    ∀ s m i j,
      |Phi W s m i j - 1 / (N : ℝ)| ≤ theta N δ * beta N Q δ ^ m := by sorry

end AggGameNet.Sync
