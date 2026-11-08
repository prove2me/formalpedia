-- Prove2me | Theorems.Thm_AsymSpecConn_corollary_3_10
-- name    : AsymSpecConn.corollary_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:40:53.673715+00:00
-- url     : https://prove2.me/theorems/b9a3bb10-e691-4a1d-bd6f-eb5d4c13acff
-- title:
--   Corollary 3.10 — paths in $\Delta(s_1,\dots,s_q)$ to $(R_i(s_1),\dots,R_i(s_q))$
-- statement:
--   Let $k\ge2$, $i\in[k]$ and $s_1,\dots,s_q\in\mathcal S$, where $\mathcal S$ is the semiring of complex $k$-tensors. Then every point of $\Delta(s_1,\dots,s_q)$ is joined by a path inside this set to $(R_i(s_1),\dots,R_i(s_q))$. In particular $\Delta(s_1,\dots,s_q)$ is path-connected, and for every $s\in\mathcal S$ the set $\Delta(s)$ is a closed interval.
--
--   This is the interval clause of the main theorem, for finitely many tensors at once.
--
--   Differences from the source:
--
--   - encoding: S, complex k-tensors up to equivalence, with legs V_1,…,V_k → MME.TensorQ ℂ k with legs indexed by Fin k (0-based) in Type; reason: Lean convention; every finite-dimensional space has an isomorphic copy in Type
--   - encoding: closed interval → ∃ a b, a ≤ b and the whole value set equals Set.Icc a b; reason: the standard rendering of a nonempty closed interval, possibly a point
--   - encoding: joined by a path → JoinedIn the value set; reason: the proof of Corollary 2.11 gives a path in Δ(s_1,…,s_q), and this is the reading of p.26
-- source:
--   Vrana and Zuiddam, The asymptotic spectrum of tensors is connected, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…), Corollary 3.10, p.26

import Mathlib
import Definitions.Def_mme_tensor_quotient
import Definitions.Def_AsymSpecConn_Spectrum
import Definitions.Def_AsymSpecConn_tensorPreorder
import Definitions.Def_AsymSpecConn_flatRank

set_option autoImplicit false

open scoped NNReal

namespace AsymSpecConn

/-- **Corollary 3.10** (p.26 of Vrana and Zuiddam, *The asymptotic spectrum of tensors is connected*, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…)): "Let i ∈ [k] and s1, …, sq ∈ S. Then
every point of ∆(s1, …, sq) is joined by a path to (Ri(s1), …, Ri(sq)). In particular
∆(s1, …, sq) is path-connected, and for every s ∈ S, ∆(s) is a closed interval."

**Formalization Note** `Δ` is the asymptotic spectrum of `S_ℂ = MME.TensorQ ℂ k`, `k ≥ 2`;
`Δ(s₁, …, s_q)` is `valueSet`; paths lie inside it (`JoinedIn`); "closed interval" is `[a, b]` with
`a ≤ b`, equal to `Δ(s)`. Legs are `Fin k` (0-based). -/
theorem corollary_3_10 {k : ℕ} (hk : 2 ≤ k) (i : Fin k) {q : ℕ} (s : Fin q → MME.TensorQ ℂ k) :
    (∀ x ∈ valueSet (MME.TensorQ ℂ k) (tensorPreorder ℂ hk) s,
      JoinedIn (valueSet (MME.TensorQ ℂ k) (tensorPreorder ℂ hk) s) x
        (fun j => (flatRankQ hk i (s j) : ℝ))) ∧
    IsPathConnected (valueSet (MME.TensorQ ℂ k) (tensorPreorder ℂ hk) s) ∧
    (∀ s₀ : MME.TensorQ ℂ k, ∃ a b : ℝ, a ≤ b ∧
      Set.range (fun f : ↥(tensorSpectrum hk) => ((f.1 s₀ : ℝ≥0) : ℝ)) = Set.Icc a b) := by sorry

end AsymSpecConn
