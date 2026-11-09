-- Prove2me | Theorems.Thm_CondGeoVerif_eq_B_2
-- name    : CondGeoVerif.eq_B_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:37:16.910201+00:00
-- url     : https://prove2.me/theorems/f9cf7e82-b20d-46c9-b2a3-e9d9879a0b39
-- title:
--   (B.2) — $R_{P_V}(h_0)-R_{P_V}(h_V)=\Gamma\ge g$ and $\inf_{h}R_{P_V}(h)\le\eta-g$
-- statement:
--   Let $k\ge1$, $0<\eta<1/2$, $f,g'$ Borel rules on $\mathbb R^k$, $A$ a contraction, $j\in\{0,1\}$, and let $e$ be a jointly measurable allocation with $e(u,\cdot)\in\mathcal E_j$ for every $u$ and gain $\Gamma=\mathbb E[2e(U,G)D_{f,g',A}(U,G)-D_{f,g',A}(U,G)]\ge g$ (B.1). Write $X=(U,Z)\in\mathbb R^{k+D}$ and let $V\in\mathbb R^{D\times k}$ be orthonormal. Let $P_V$ be the alternative: Gaussian features, and error probability $e(U,V^\top Z)$ around the anchor $h_0(U,Z)=f(U)$; let $Q$ be the random-noise anchor. Then $R_{P_V}(h_0)=\eta=R_Q(h_0)$, the competing function $h_V(U,Z)=g'(A^\top U+B_AV^\top Z)$ belongs to $\mathcal H_{F,k+D}$ for every family $F\ni g'$, and
--   $$R_{P_V}(h_0)-R_{P_V}(h_V)=\Gamma\ge g,\qquad\inf_{h\in\mathcal H_{F,k+D}}R_{P_V}(h)\le\eta-g.\qquad(B.2)$$
--   The alternatives violate the anchor's optimality by $g$, so a sound verifier must reject or output a better predictor.
--
--   Differences from the source:
--   - generalization: the fixed-rule comparator f(AᵀU + BVᵀZ) and the class H_{f,d} → a competitor rule g′ and the class H_{F,d} of any family F ∋ g′; reason: the fixed-rule (B.2) is g′ = f, F = {f}; the family form is p.23
--   - generalization: e from Lemma B.2 with ξ = γ/4, g = γ/2 → any jointly measurable allocation with sections in E_j and gain at least g; reason: the paper's allocation is one such
--   - encoding: P_V and Q defined by their regressions → any probability measures with the characterizing property IsLabelLaw; reason: the property determines each law uniquely
--   - encoding: labels and rule values in {−1, 1} → Bool, with true for +1; reason: Lean convention; the same instances
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), §B.2, p.25 (PDF p.28), eq. (B.2); family form, proof of Theorem A.5, p.23 (PDF p.26)

import Mathlib
import Definitions.Def_CondGeoVerif_hiddenErr
import Definitions.Def_CondGeoVerif_risk

set_option autoImplicit false

open MeasureTheory ProjLikeRetr.Stiefel
open scoped Matrix

namespace CondGeoVerif

/-- **The alternative has a better comparator (B.2)** (Chen, *The Conditional Geometry of
Statistical Verification*, manuscript, October 2026, sha256 07a66d18…, §B.2, p.25 = PDF p.28;
family form, proof of Theorem A.5, p.23). Write `X = (U, Z)`, `Z ∼ N(0, I_D)`, `d = k + D`, let
`V ∈ ℝ^{D×k}` be orthonormal, `A` a contraction, `B = (I_k − AᵀA)^{1/2}`, and let `e` be a jointly
measurable allocation with `e(u, ·) ∈ E_j` for every `u` and gain `Γ = E[2eD_A − D_A] ≥ g` (B.1).
The alternative `P_V` has feature marginal `N(0, I_d)` and error probability `e(U, VᵀZ)` around
the anchor `h₀(U, Z) = f(U)`. Then `R_{P_V}(h₀) = η = R_Q(h₀)`, the competing function
`h_V(U, Z) = g(AᵀU + BVᵀZ)` belongs to the projection class, and the paired-risk identity gives
`R_{P_V}(h₀) − R_{P_V}(h_V) = Γ ≥ g` and `inf_{h ∈ H} R_{P_V}(h) ≤ η − g`.

**Formalization Note** The competitor rule `g'` and the class `H = H_{F,d}` for any family `F ∋ g'`
are those of the family form; the fixed-rule (B.2) is `g' = f`, `F = {f}`. The paper's gain floor
`g = γ/2` is the variable `gmin`. `P_V` and the anchor `Q` are given through their characterizing
property `IsLabelLaw`. -/
theorem eq_B_2 {k D : ℕ} (hk : 1 ≤ k) {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1 / 2)
    (f g' : Vec k → Bool) (hf : Measurable f) (hg' : Measurable g')
    (A : Matrix (Fin k) (Fin k) ℝ) (hA : IsContraction A) (j : Fin 2)
    (e : Vec k → Vec k → ℝ) (he : Measurable (fun p : Vec k × Vec k => e p.1 p.2))
    (heE : ∀ u, e u ∈ errorAllocs j η k) (gmin : ℝ) (hgain : gmin ≤ gainOf e f g' A)
    (V : Matrix (Fin D) (Fin k) ℝ) (hV : V ∈ stiefel D k)
    (Q : ProbabilityMeasure (Vec (k + D) × Bool))
    (hQ : IsLabelLaw (Q : Measure (Vec (k + D) × Bool)) (fun x => f (splitU x)) (fun _ => η))
    (PV : ProbabilityMeasure (Vec (k + D) × Bool))
    (hPV : IsLabelLaw (PV : Measure (Vec (k + D) × Bool)) (fun x => f (splitU x)) (hiddenErr e V))
    (F : Set (Vec k → Bool)) (hg'F : g' ∈ F) :
    risk (PV : Measure (Vec (k + D) × Bool)) (fun x => f (splitU x)) = η ∧
    risk (Q : Measure (Vec (k + D) × Bool)) (fun x => f (splitU x)) = η ∧
    hiddenComp g' A V ∈ projClass F (k + D) ∧
    risk (PV : Measure (Vec (k + D) × Bool)) (fun x => f (splitU x)) -
        risk (PV : Measure (Vec (k + D) × Bool)) (hiddenComp g' A V) = gainOf e f g' A ∧
    opt (PV : Measure (Vec (k + D) × Bool)) (projClass F (k + D)) ≤ η - gmin := by sorry

end CondGeoVerif
