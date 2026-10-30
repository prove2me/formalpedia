-- Prove2me | Theorems.Thm_DerivativeChainPrefixLaws_uniform_labelled_histories
-- name    : DerivativeChainPrefixLaws.uniform_labelled_histories
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T06:45:49.594494+00:00
-- url     : https://prove2.me/theorems/b60b5eb7-aae5-472b-ac98-e9484851077b
-- title:
--   Uniform labelled histories
-- statement:
--   For each natural number $k$, write $I_k=\{0,\ldots,k-1\}$, with $I_0=\varnothing$. Let $n\in \mathbb N$, $K\colon \prod_{k\in \mathbb N} \bigl(I_{\left(k + 1\right)}\longrightarrow \bigl(I_{\left(k + 2\right)}\longrightarrow \mathbb R\bigr)\bigr)$. Assume
--
--   $$
--   \begin{aligned}
--   &\forall k_{1}\in \mathbb N,\quad \bigl(\left(k_{1} < n\right)\Longrightarrow \forall i\in I_{\left(k_{1} + 1\right)},\quad \forall j\in I_{\left(k_{1} + 2\right)},\quad \left(0 \le K\!\left(k_{1}, i, j\right)\right)\bigr)\\
--   &\forall k_{2}\in \mathbb N,\quad \bigl(\left(k_{2} < n\right)\Longrightarrow \forall i_{1}\in I_{\left(k_{2} + 1\right)},\quad \left(\sum_{j_{1}\in \mathsf{univ}} K\!\left(k_{2}, i_{1}, j_{1}\right) = 1\right)\bigr)\\
--   &\forall k_{3}\in \mathbb N,\quad \bigl(\left(k_{3} < n\right)\Longrightarrow \forall j_{2}\in I_{\left(k_{3} + 2\right)},\quad \left(\sum_{i_{2}\in \mathsf{univ}} \left(\left(\left(k_{3} + 1\right)\right)^{-1} \, K\!\left(k_{3}, i_{2}, j_{2}\right)\right) = \left(\left(k_{3} + 2\right)\right)^{-1}\right)\bigr)
--   \end{aligned}
--   $$
--
--   Then
--
--   $$
--   \exists κ\in \mathsf{Type},\quad \exists \mathit{inst}\in \operatorname{Fintype}\!\left(κ\right),\quad \exists w\colon \bigl(κ\longrightarrow \mathbb R\bigr),\quad \exists \mathit{slots}\colon \bigl(κ\longrightarrow \prod_{k_{4}\in \mathbb N} I_{\left(k_{4} + 1\right)}\bigr),\quad \left(\forall i_{3}\in κ,\quad \left(0 \le w\!\left(i_{3}\right)\right) \land \left(\left(\sum_{i_{4}\in \mathsf{univ}} w\!\left(i_{4}\right) = 1\right) \land \left(\forall k_{5}\in \mathbb N,\quad \bigl(\left(k_{5} \le n\right)\Longrightarrow \forall f\in \bigl(I_{\left(k_{5} + 1\right)}\longrightarrow \mathbb R\bigr),\quad \left(\sum_{i_{5}\in \mathsf{univ}} \left(w\!\left(i_{5}\right) \, f\!\left(\mathit{slots}\!\left(i_{5}, k_{5}\right)\right)\right) = \sum_{j_{3}\in \mathsf{univ}} \left(\left(\left(k_{5} + 1\right)\right)^{-1} \, f\!\left(j_{3}\right)\right)\right)\bigr) \land \forall k_{6}\in \mathbb N,\quad \bigl(\left(k_{6} < n\right)\Longrightarrow \forall f_{1}\in \bigl(I_{\left(k_{6} + 1\right)}\longrightarrow \bigl(I_{\left(k_{6} + 2\right)}\longrightarrow \mathbb R\bigr)\bigr),\quad \left(\sum_{i_{6}\in \mathsf{univ}} \left(w\!\left(i_{6}\right) \, f_{1}\!\left(\mathit{slots}\!\left(i_{6}, k_{6}\right), \mathit{slots}\!\left(i_{6}, \left(k_{6} + 1\right)\right)\right)\right) = \sum_{j_{4}\in \mathsf{univ}} \left(\left(\left(k_{6} + 1\right)\right)^{-1} \, \sum_{l\in \mathsf{univ}} \left(K\!\left(k_{6}, j_{4}, l\right) \, f_{1}\!\left(j_{4}, l\right)\right)\right)\right)\bigr)\right)\right)\right)
--   $$
--
--   Weight each complete slot path by the product of its transition weights. Finite summation of stochastic rows gives the uniform marginals and exact test-function expectations.
--
--   Formalization Note. Natural-number subtraction is truncated. Named functions, index embeddings and field projections use their exact imported definitions.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/prefix_laws/UniformHistoryLabels.lean, lines 11-76, SHA-256 1f0361a66b4b557c05d4a9a84918f0f9f7d1e713c917fe0a9ca672d540f74e7c. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.

import Mathlib
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainFiniteHistory
end DerivativeChainFiniteHistory
namespace DerivativeChainPhaseLock
end DerivativeChainPhaseLock
namespace DerivativeChainPrefixLaws
end DerivativeChainPrefixLaws
namespace DerivativeChainPrivate
end DerivativeChainPrivate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open Polynomial DerivativeChainContinuation DerivativeChainPrivate
open DerivativeChainPrefixLaws

theorem DerivativeChainPrefixLaws.uniform_labelled_histories (n : ℕ)
    (K : (k : ℕ) → Fin (k+1) → Fin (k+2) → ℝ)
    (hK : ∀ k<n,∀ i j,0 ≤ K k i j)
    (hKs : ∀ k<n,∀ i,∑ j,K k i j=1)
    (hKcol : ∀ k<n,∀ j,(∑ i,(k+1:ℝ)⁻¹*K k i j)=(k+2:ℝ)⁻¹) :
    ∃ (κ : Type) (inst : Fintype κ),letI := inst;
      ∃ (w : κ → ℝ) (slots : κ → (k : ℕ) → Fin (k+1)),
        (∀ i,0 ≤ w i) ∧ (∑ i,w i=1) ∧
        (∀ k≤n,∀ f : Fin (k+1) → ℝ,
          (∑ i,w i*f (slots i k))=∑ j,(k+1:ℝ)⁻¹*f j) ∧
        ∀ k<n,∀ f : Fin (k+1) → Fin (k+2) → ℝ,
          (∑ i,w i*f (slots i k) (slots i (k+1)))=
            ∑ j,(k+1:ℝ)⁻¹*(∑ l,K k j l*f j l) := by sorry
