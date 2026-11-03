-- Prove2me | Theorems.Thm_EnvelopeMSLP_lemma_1
-- name    : EnvelopeMSLP.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:26:49.128062+00:00
-- url     : https://prove2.me/theorems/3319bbe4-f834-427a-ad79-ab6af5762d0c
-- title:
--   Lemma 1 — $R_\beta$ is a finite union of connected smooth manifolds
-- statement:
--   Let $\mathcal P(\mathcal D)$ be a problem of form (4) with data $\mathcal D=(c,D,b)\in\mathbb R^N$, $D$ of dimensions $m\times n$, and let $\beta$ be a basis. Then
--   $$R_\beta=\{\mathcal D:\beta\text{ is an optimal basis for }\mathcal P(\mathcal D)\}=\bigcup_{i=1}^I\mathcal S_i$$
--   for finitely many connected sets $\mathcal S_i\subseteq\mathbb R^N$, each a smooth manifold diffeomorphic to an open cube $(0,1)^{n_i}$ with $0\le n_i\le N$.
--
--   This stratification by smooth cells is the geometric content behind the behaviour of an optimal basis along a parameter.
--
--   Differences from the source:
--   - reading: connected smooth manifolds of varying dimensions → images of open cubes under smooth embeddings, connected; reason: this is the form the proof on p.9 gives: diffeomorphisms hᵢ : (0,1)^nᵢ → Sᵢ with 0 ≤ nᵢ ≤ N
--   - reading: β ⊆ [n] with |β| = m → an injection Fin m ↪ Fin n; reason: optimality of β does not depend on the order of its columns
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), Lemma 1, p.8, with its proof, p.9

import Mathlib
import Definitions.Def_EnvelopeMSLP_IsOptimalBasis
import Definitions.Def_EnvelopeMSLP_lpData
import Definitions.Def_EnvelopeMSLP_IsSmoothCell

namespace EnvelopeMSLP

/-- **Lemma 1: `R_β` is a finite union of connected smooth manifolds.** Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), Lemma 1, p.8, with the
manifolds as in its proof, p.9. Fix an ordered basis `β`. The set of stacked data `(D, b, c) ∈ ℝ^N`
for which `β` is an optimal basis of form (4) is a finite union of connected sets, each a smooth embedded
image of an open cube of dimension at most `N`.

**Formalization Note.** `I = 0` covers an empty `R_β`. -/
theorem lemma_1 {m n : ℕ} (β : Fin m ↪ Fin n) :
    ∃ (I : ℕ) (S : Fin I → Set (LPIndex m n → ℝ)),
      {d | ∃ (D : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ),
          d = lpData D b c ∧ IsOptimalBasis D b c β} = ⋃ i, S i ∧
      ∀ i, IsSmoothCell (S i) ∧ IsConnected (S i) := by sorry

end EnvelopeMSLP
