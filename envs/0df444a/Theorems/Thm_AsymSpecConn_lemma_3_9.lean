-- Prove2me | Theorems.Thm_AsymSpecConn_lemma_3_9
-- name    : AsymSpecConn.lemma_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:41:30.785324+00:00
-- url     : https://prove2.me/theorems/baa8c796-b26c-4882-ad26-2a5bcde5458e
-- title:
--   Lemma 3.9 — every pair $f,R_i$ has the $\mathcal A_i$-cover property with $\kappa_a(n)=1$
-- statement:
--   Let $k\ge2$ and $f\in\Delta$.
--
--   1. For every $a\in\mathcal A_1$ and all $s_1,s_2\in\mathcal S$ with $a\le s_1\oplus s_2$,
--   $$1\le\frac{f(s_1)}{f(a)}+\frac{R_1(s_2)}{R_1(a)}.$$
--   2. The pair $f,R_1$ has the $\mathcal A_1$-cover property with $\kappa_a(n)=1$.
--
--   This verifies, for tensors, the cover hypothesis of the interpolation theorem with fixed endpoint a flattening rank.
--
--   The Lean statement holds for every leg $i$.
--
--   Differences from the source:
--
--   - encoding: S, complex k-tensors up to equivalence, with legs V_1,…,V_k → MME.TensorQ ℂ k with legs indexed by Fin k (0-based) in Type; reason: Lean convention; every finite-dimensional space has an isomorphic copy in Type
--   - generalization: leg 1, A_1 and R_1 → every leg i, A_i and R_i; reason: the source uses the lemma for every leg after relabelling (p.26); i = 0 is the source's leg 1
--   - encoding: the pair f, R_1 has the cover property with κ_a(n) = 1 → for every spectral point g equal to R_i: HasACoverProperty for ![f, g], and CoverBound with κ = 1 for every a in A_i; reason: the spectral point R_i exists by §3, p.21; this states the cover property and its explicit witness
-- source:
--   Vrana and Zuiddam, The asymptotic spectrum of tensors is connected, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…), Lemma 3.9, p.26

import Mathlib
import Definitions.Def_mme_tensor_quotient
import Definitions.Def_AsymSpecConn_Spectrum
import Definitions.Def_AsymSpecConn_HasACoverProperty
import Definitions.Def_AsymSpecConn_tensorPreorder
import Definitions.Def_AsymSpecConn_flatRank
import Definitions.Def_AsymSpecConn_irreducibleSet

set_option autoImplicit false

open scoped NNReal

namespace AsymSpecConn

/-- **Lemma 3.9** (p.26 of Vrana and Zuiddam, *The asymptotic spectrum of tensors is connected*, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…)), for every leg `i`: "Let f ∈ ∆. (i) For
every a ∈ A1 and all s1, s2 ∈ S with a ≤ s1 ⊕ s2, 1 ≤ f(s1)/f(a) + R1(s2)/R1(a). (ii) The pair
f, R1 has the A1-cover property with κa(n) = 1."

**Formalization Note** Stated for an arbitrary leg `i` (leg 1 is `i = 0`; the paper relabels the
legs, p.26). `s₁ ⊕ s₂` is `s₁ + s₂` in `S_ℂ`; `R_i` on classes is `flatRankQ`. In (ii) `R_i` is
the spectral point `g` with `g = R_i` (it exists, §3 p.21); the clause gives both the cover
property and the explicit witness `κ_a ≡ 1`. Division in `ℝ` (both denominators are positive for
`a ≠ 0`). -/
theorem lemma_3_9 {k : ℕ} (hk : 2 ≤ k) (i : Fin k) (f : ↥(tensorSpectrum hk)) :
    (∀ a ∈ irreducibleSet hk i, ∀ s₁ s₂ : MME.TensorQ ℂ k,
      (tensorPreorder ℂ hk).le a (s₁ + s₂) →
        (1 : ℝ) ≤ ((f.1 s₁ : ℝ≥0) : ℝ) / ((f.1 a : ℝ≥0) : ℝ) +
          (flatRankQ hk i s₂ : ℝ) / (flatRankQ hk i a : ℝ)) ∧
    (∀ g : ↥(tensorSpectrum hk), (∀ s, g.1 s = (flatRankQ hk i s : ℝ≥0)) →
      HasACoverProperty (tensorPreorder ℂ hk) (irreducibleSet hk i) ![f, g] ∧
      ∀ a ∈ irreducibleSet hk i,
        CoverBound (tensorPreorder ℂ hk) ![f, g] a (fun _ => 1)) := by sorry

end AsymSpecConn
