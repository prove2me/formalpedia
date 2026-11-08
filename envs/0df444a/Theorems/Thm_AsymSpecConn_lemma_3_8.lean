-- Prove2me | Theorems.Thm_AsymSpecConn_lemma_3_8
-- name    : AsymSpecConn.lemma_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:41:23.799576+00:00
-- url     : https://prove2.me/theorems/52f174c7-200a-4565-807e-4a68dcc6e522
-- title:
--   Lemma 3.8 — reverse monotonicity, $\frac{R_i(b)}{R_i(a)}f(a)\le f(b)$
-- statement:
--   Let $k\ge2$, let $a\in\mathcal A_1$ lie in $V_1\otimes\dots\otimes V_k$, and let $b=(\pi\otimes\mathrm{Id}\otimes\dots\otimes\mathrm{Id})a$ for a linear map $\pi:V_1\to W$. Then for every $f\in\Delta$,
--   $$\frac{R_1(b)}{R_1(a)}f(a)\le f(b).$$
--
--   Since $b\le a$ gives $f(b)\le f(a)$, this bounds how much a spectral point can drop under restriction.
--
--   The Lean statement holds for every leg $i$ and allows linear bijections on the other legs.
--
--   Differences from the source:
--
--   - encoding: S, complex k-tensors up to equivalence, with legs V_1,…,V_k → MME.TensorQ ℂ k with legs indexed by Fin k (0-based) in Type; reason: Lean convention; every finite-dimensional space has an isomorphic copy in Type
--   - generalization: leg 1 and A_1 → every leg i and A_i; reason: the source uses the lemma for every leg after relabelling (p.26); i = 0 is the source's leg 1
--   - generalization: b = (π ⊗ Id ⊗ ⋯ ⊗ Id)a → Y with Y.t = (π_1 ⊗ ⋯ ⊗ π_k)X.t, π_i arbitrary and π_j a linear bijection for j ≠ i; reason: dependent leg types make Id awkward; taking Y.V j = X.V j and π_j = Id for j ≠ i gives the source's b, and bijections on the other legs do not change the class or R_i
-- source:
--   Vrana and Zuiddam, The asymptotic spectrum of tensors is connected, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…), Lemma 3.8, p.25

import Mathlib
import Definitions.Def_mme_tensor_quotient
import Definitions.Def_AsymSpecConn_Spectrum
import Definitions.Def_AsymSpecConn_tensorPreorder
import Definitions.Def_AsymSpecConn_flatRank
import Definitions.Def_AsymSpecConn_irreducibleSet

set_option autoImplicit false

open scoped NNReal

namespace AsymSpecConn

/-- **Lemma 3.8** (p.25 of Vrana and Zuiddam, *The asymptotic spectrum of tensors is connected*, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…)), for every leg `i`: "Let a ∈ A1 lie in
V1 ⊗ ⋯ ⊗ Vk. Let b := (π ⊗ Id ⊗ ⋯ ⊗ Id)a for some linear map π : V1 → W. Then for every f ∈ ∆
we have (R1(b)/R1(a)) f(a) ≤ f(b)."

**Formalization Note** Stated for an arbitrary leg `i` (the paper uses it "after relabelling the
legs", p.26; leg 1 is `i = 0`). `a` is a tensor `X` whose class lies in `A_i`; `b` is a tensor `Y`
with `Y.t = (π₁ ⊗ ⋯ ⊗ π_k) X.t` where `π_i` is the linear map `π` and every other `π_j` is a
linear isomorphism (so `Y` is equivalent to the paper's `(π ⊗ Id ⊗ ⋯ ⊗ Id) a`). Division in `ℝ`
(`R_i(a) > 0` since `a ≠ 0`). -/
theorem lemma_3_8 {k : ℕ} (hk : 2 ≤ k) (i : Fin k) (X : MME.TensorObj ℂ k)
    (hX : MME.TensorQ.toQ X ∈ irreducibleSet hk i) (Y : MME.TensorObj ℂ k)
    (π : ∀ j, X.V j →ₗ[ℂ] Y.V j) (hπ : ∀ j, j ≠ i → Function.Bijective (π j))
    (hY : PiTensorProduct.map π X.t = Y.t) (f : ↥(tensorSpectrum hk)) :
    (flatRank hk i Y : ℝ) / (flatRank hk i X : ℝ) * ((f.1 (MME.TensorQ.toQ X) : ℝ≥0) : ℝ) ≤
      ((f.1 (MME.TensorQ.toQ Y) : ℝ≥0) : ℝ) := by sorry

end AsymSpecConn
