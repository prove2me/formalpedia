-- Prove2me | Theorems.Thm_AsymSpecConn_flatRank_mem_spectrum
-- name    : AsymSpecConn.flatRank_mem_spectrum
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:40:47.815294+00:00
-- url     : https://prove2.me/theorems/6530ee01-b6dd-4acd-9511-2c21be19b8b5
-- title:
--   §3, p.21 — every flattening rank $R_i$ is a spectral point
-- statement:
--   Let $F$ be a field, $k\ge2$ and $i\in[k]$. The $i$-flattening rank is a spectral point of $\mathcal S_F$: there is an element $g$ of the asymptotic spectrum $\Delta_F$ with $g(s)=R_i(s)$ for every class $s$.
--
--   The flattening ranks are the fixed endpoints of the paths in the main theorem.
--
--   Differences from the source:
--
--   - encoding: S_F, k-tensors over F up to equivalence, with legs V_1,…,V_k → MME.TensorQ with legs indexed by Fin k (0-based) in one universe; reason: Lean convention; every finite-dimensional space has an isomorphic copy in that universe
--   - encoding: R_i ∈ Δ_F → ∃ g in the spectrum with g s = flatRankQ hk i s for every class s; reason: R_i is ℕ-valued in Lean; this says that the function, cast to ℝ≥0, belongs to the spectrum
-- source:
--   Vrana and Zuiddam, The asymptotic spectrum of tensors is connected, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…), §3, p.21

import Mathlib
import Definitions.Def_mme_tensor_quotient
import Definitions.Def_AsymSpecConn_Spectrum
import Definitions.Def_AsymSpecConn_tensorPreorder
import Definitions.Def_AsymSpecConn_flatRank

set_option autoImplicit false

open scoped NNReal

namespace AsymSpecConn

/-- **§3, p.21** of Vrana and Zuiddam, *The asymptotic spectrum of tensors is connected*, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…): "For every i ∈ [k] we have Ri ∈ ∆F."

That is: the `i`-flattening rank, as a function on `S_F`, is a spectral point.

**Formalization Note** `R_i` on classes is `flatRankQ hk i` (well defined since flattening rank is
monotone under restriction); the statement asserts a spectral point `g` of `S_F` equal to it.
Legs are `Fin k` (0-based). Every field `F`, as printed; `k ≥ 2`. -/
theorem flatRank_mem_spectrum (F : Type*) [Field F] {k : ℕ} (hk : 2 ≤ k) (i : Fin k) :
    ∃ g ∈ Spectrum (MME.TensorQ F k) (tensorPreorder F hk),
      ∀ s : MME.TensorQ F k, g s = (flatRankQ hk i s : ℝ≥0) := by sorry

end AsymSpecConn
