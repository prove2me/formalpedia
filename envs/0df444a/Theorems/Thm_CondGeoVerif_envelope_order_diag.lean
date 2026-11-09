-- Prove2me | Theorems.Thm_CondGeoVerif_envelope_order_diag
-- name    : CondGeoVerif.envelope_order_diag
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:28:53.205452+00:00
-- url     : https://prove2.me/theorems/97894e25-a64a-4904-9971-6b14c0f3dd61
-- title:
--   $J_1\le J_0$ and $J_j(f,f,I_k;\eta)=0$
-- statement:
--   Let $k\ge1$ and $0<\eta<1/2$. For all Borel rules $f,g:\mathbb R^k\to\{-1,1\}$ and every contraction $A\in\mathbb R^{k\times k}$,
--   $$J_1(f,g,A;\eta)\le J_0(f,g,A;\eta),$$
--   and for every Borel $f$ and $j\in\{0,1\}$, $J_j(f,f,I_k;\eta)=0$.
--
--   The ordering makes the three rows of the dimension classification exhaustive.
--
--   Differences from the source:
--   - generalization: ordered pairs f, g from a totally bounded family F → all Borel rules f, g; reason: the statement is about each pair; family members are Borel rules
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), §3, p.4 (PDF p.7)

import Mathlib
import Definitions.Def_CondGeoVerif_Jprog

set_option autoImplicit false

open MeasureTheory

namespace CondGeoVerif

/-- **Ordering and the diagonal** (Chen, *The Conditional Geometry of Statistical Verification*,
manuscript, October 2026, sha256 07a66d18…, §3, p.4 = PDF p.7): "Always `J₁ ≤ J₀` and
`J_j(f, f, I_k; η) = 0`." For Borel rules `f, g : ℝᵏ → {−1, 1}`, every contraction `A` and
`0 < η < 1/2`, `J₁(f, g, A; η) ≤ J₀(f, g, A; η)`, and `J_j(f, f, I_k; η) = 0` for `j ∈ {0, 1}`.

**Formalization Note** Stated for every pair of Borel rules, not only pairs from a family. -/
theorem envelope_order_diag {k : ℕ} (hk : 1 ≤ k) {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1 / 2) :
    (∀ f g : Vec k → Bool, Measurable f → Measurable g →
      ∀ A : Matrix (Fin k) (Fin k) ℝ, IsContraction A → Jprog 1 f g A η ≤ Jprog 0 f g A η) ∧
    (∀ f : Vec k → Bool, Measurable f → ∀ j : Fin 2, Jprog j f f 1 η = 0) := by sorry

end CondGeoVerif
