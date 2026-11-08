-- Prove2me | Theorems.Thm_AsymSpecConn_theorem_3_1
-- name    : AsymSpecConn.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:40:56.043209+00:00
-- url     : https://prove2.me/theorems/0ca2e959-3d42-449f-ab6f-fd6d38e36e43
-- title:
--   Theorem 3.1 — the asymptotic spectrum of complex $k$-tensors is path-connected and contractible
-- statement:
--   Let $k\ge2$, let $\mathcal S$ be the semiring of complex $k$-tensors up to equivalence, with direct sum, Kronecker product and restriction, and let $\Delta$ be its asymptotic spectrum: all monotone semiring homomorphisms $f:\mathcal S\to\mathbb R_{\ge0}$ with $f(1)=1$, with the topology of pointwise convergence. Let $R_i$ be the $i$-flattening rank. Then:
--
--   1. $\Delta$ is path-connected: for every $i\in[k]$ and every $f\in\Delta$ there is a path in $\Delta$ from $f$ to $R_i$.
--   2. For every $s\in\mathcal S$, the set
--   $$\Delta(s)=\{f(s):f\in\Delta\}$$
--   is a closed interval.
--   3. $\Delta$ is contractible.
--
--   This answers a question of Strassen on the structure of the asymptotic spectrum of tensors.
--
--   **Formalization Note** The statement quantifies over every $k\ge2$, the range of the source's Theorem 1.1 and §3; its abstract says $k\ge3$, which the theorem covers.
--
--   Differences from the source:
--
--   - encoding: S, complex k-tensors up to equivalence, with legs V_1,…,V_k → MME.TensorQ ℂ k with legs indexed by Fin k (0-based) in Type; reason: Lean convention; every finite-dimensional space has an isomorphic copy in Type
--   - encoding: a path in Δ from f to R_i → ∃ g in Δ with g s = flatRankQ hk i s for every s, and Joined f g in the subtype Δ; reason: R_i is ℕ-valued in Lean; such a g is unique, and its existence is part of the source's claim
--   - encoding: closed interval → ∃ a b, a ≤ b and the whole value set equals Set.Icc a b; reason: the standard rendering of a nonempty closed interval, possibly a point
--   - encoding: contractible, in the sense of p.19 → Mathlib's ContractibleSpace; reason: equivalent: Mathlib's definition is that the identity is nullhomotopic
-- source:
--   Vrana and Zuiddam, The asymptotic spectrum of tensors is connected, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…), Theorem 3.1, p.21 (= Theorem 1.1, p.8)

import Mathlib
import Definitions.Def_mme_tensor_quotient
import Definitions.Def_AsymSpecConn_Spectrum
import Definitions.Def_AsymSpecConn_tensorPreorder
import Definitions.Def_AsymSpecConn_flatRank

set_option autoImplicit false

open scoped NNReal

namespace AsymSpecConn

/-- **Theorem 3.1** (p.21 of Vrana and Zuiddam, *The asymptotic spectrum of tensors is connected*, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…); = Theorem 1.1, p.8): "The asymptotic
spectrum ∆ of complex k-tensors is path-connected: for every i ∈ [k] and every f ∈ ∆ there is a
path in ∆ from f to Ri. For every s ∈ S, the set ∆(s) is a closed interval. In fact, ∆ is
contractible." (Standing assumption of §3: k ≥ 2.)

**Formalization Note** `S = S_ℂ` is `MME.TensorQ ℂ k` (complex `k`-tensors up to equivalence, with
direct sum, Kronecker product and restriction); `Δ` is `↥(tensorSpectrum hk)`: all monotone
semiring homomorphisms `S → ℝ≥0`, with the topology of pointwise convergence. `R_i` is the spectral
point `g` with `g(s) = R_i(s)` (the `i`-flattening rank, `flatRankQ`), whose existence is part of
the first clause; the path lies in `Δ` (`Joined` in the subspace). "Closed interval" is `[a, b]`
with `a ≤ b`, equal to `Δ(s)`. "Contractible" is Mathlib's `ContractibleSpace`. Legs are `Fin k`
(0-based). -/
theorem theorem_3_1 (k : ℕ) (hk : 2 ≤ k) :
    (∀ (i : Fin k) (f : ↥(tensorSpectrum hk)), ∃ g : ↥(tensorSpectrum hk),
      (∀ s : MME.TensorQ ℂ k, g.1 s = (flatRankQ hk i s : ℝ≥0)) ∧ Joined f g) ∧
    (∀ s : MME.TensorQ ℂ k, ∃ a b : ℝ, a ≤ b ∧
      Set.range (fun f : ↥(tensorSpectrum hk) => ((f.1 s : ℝ≥0) : ℝ)) = Set.Icc a b) ∧
    PathConnectedSpace ↥(tensorSpectrum hk) ∧
    ContractibleSpace ↥(tensorSpectrum hk) := by sorry

end AsymSpecConn
