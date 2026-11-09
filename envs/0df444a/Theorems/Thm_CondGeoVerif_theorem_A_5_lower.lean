-- Prove2me | Theorems.Thm_CondGeoVerif_theorem_A_5_lower
-- name    : CondGeoVerif.theorem_A_5_lower
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:41:10.023679+00:00
-- url     : https://prove2.me/theorems/0f2d451f-3080-48a4-ad5a-8fc269f48193
-- title:
--   Theorem A.5 (lower part) — a positive witness $J_j(f,g,A;\eta)=\Gamma$ gives the lower bounds of Theorem B.1
-- statement:
--   Let $F$ be a nonempty family of Borel rules $\mathbb R^K\to\{-1,1\}$, $K\ge1$, totally bounded in Gaussian disagreement, and $0<\eta<1/2$. Let $f,g\in F$, $A$ a contraction and $j\in\{0,1\}$ with $J_j(f,g,A;\eta)=\Gamma>0$, and $0<\varepsilon\le\Gamma/8$. For every $d\ge2K$, with $\ell=\lceil128\log24/(\Gamma/2)^2\rceil$, every verifier complete with probability at least $2/3$ at the known random-noise anchor $Q$ of $f$ ($\mathbb E_Q[Y\mid X]=af(X_1,\dots,X_K)$) and sound with probability at least $2/3$ against arbitrary Gaussian-marginal labels with respect to $\mathcal H_{F,d}$ satisfies
--   $$m_V+\ell>\sqrt{d-K}/(100K)\ (j=0),\qquad m_V+\ell>(d-K)/(100K^2)\ (j=1).$$
--   Interaction and improper outputs are allowed. Thus the exhaustive classification holds even when the intrinsic rule is unknown.
--
--   Differences from the source:
--   - reading: any verifier with arbitrary interaction → IVerifier: a fixed worst-case number of rounds, measurable queries and acceptance, jointly measurable output predictors; reason: the probabilities of Definition 2.1 are defined only for measurable protocols, outputs are 'measurable Boolean predictors', and bounded stopping rules are padded (p.28)
--   - generalization: soundness against every prover → soundness hypothesis only against measurable deterministic prover strategies; reason: a weaker hypothesis; the proof's simulated honest prover is a measurable randomized strategy, a mixture of deterministic ones
--   - encoding: the null Q: X ∼ N(0, I_d), E_Q[Y | X] = af(X₁, …, X_k) → any probability measure with IsLabelLaw for the base rule f(X₁, …, X_k) and constant error probability η; reason: this property determines Q uniquely
--   - encoding: ℓ = ⌈128 log 24/g²⌉, √(d − k) → natural-number ceiling, natural logarithm, real square root of d − k; reason: Lean convention
--   - encoding: labels and rule values in {−1, 1} → Bool, with true for +1; reason: Lean convention; the same instances
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), Theorem A.5, p.21 (PDF p.24), second paragraph; proof p.23 (PDF p.26)

import Mathlib
import Definitions.Def_CondGeoVerif_Jprog
import Definitions.Def_CondGeoVerif_GaussTotallyBounded
import Definitions.Def_CondGeoVerif_IVerifier

set_option autoImplicit false

open MeasureTheory

namespace CondGeoVerif

/-- **Theorem A.5 (Unknown-rule family classification), lower part** (Chen, *The Conditional
Geometry of Statistical Verification*, manuscript, October 2026, sha256 07a66d18…, p.21 =
PDF p.24; proof p.23). Let `F` be a nonempty family of Borel rules `ℝᴷ → {−1, 1}`, totally bounded
in Gaussian disagreement, and `0 < η < 1/2`. A positive witness `J_j(f, g, A; η) = Γ`
(`f, g ∈ F`, `A` a contraction, `j ∈ {0, 1}`) gives exactly the lower bounds of Theorem B.1, with
rank `K`, for `0 < ε ≤ Γ/8`: for `d ≥ 2K`, with `ℓ = ⌈128 log 24/(Γ/2)²⌉`, any verifier complete
with probability at least `2/3` at the known random-noise anchor `Q` of `f`
(`E_Q[Y | X] = af(X₁, …, X_K)`) and sound with probability at least `2/3` against arbitrary
Gaussian-marginal labels with respect to `H_{F,d}` satisfies `m_V + ℓ > √(d − K)/(100K)` for
`j = 0` and `m_V + ℓ > (d − K)/(100K²)` for `j = 1`.

**Formalization Note** Same verifier model and anchor encoding as `theorem_B_1`; soundness is
with respect to the whole union `H_{F,d}`, and completeness is needed only at the anchor of the
witness's first rule. -/
theorem theorem_A_5_lower {K d : ℕ} (hK : 1 ≤ K) (hd : 2 * K ≤ d) (F : Set (Vec K → Bool))
    (hFne : F.Nonempty) (hFm : ∀ f ∈ F, Measurable f) (hFtb : GaussTotallyBounded F)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1 / 2) (f g : Vec K → Bool) (hfF : f ∈ F) (hgF : g ∈ F)
    (A : Matrix (Fin K) (Fin K) ℝ) (hA : IsContraction A) (j : Fin 2) (Γ : ℝ)
    (hΓ : Jprog j f g A η = Γ) (hΓ0 : 0 < Γ) (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ Γ / 8)
    (Q : ProbabilityMeasure (Vec d × Bool))
    (hQ : IsLabelLaw (Q : Measure (Vec d × Bool)) (frameRule f (coordFrame d K)) (fun _ => η))
    (V : IVerifier d) (hcomp : ICompleteAt V Q (projClass F d) ε (1 / 3))
    (hsound : ISound V (projClass F d) ε (1 / 3)) :
    let ℓ : ℕ := ⌈128 * Real.log 24 / (Γ / 2) ^ 2⌉₊
    (j = 0 → Real.sqrt ((d : ℝ) - K) / (100 * K) < (V.m : ℝ) + ℓ) ∧
    (j = 1 → ((d : ℝ) - K) / (100 * K ^ 2) < (V.m : ℝ) + ℓ) := by sorry

end CondGeoVerif
