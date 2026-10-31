-- Prove2me | Theorems.Thm_ContactTopology_smooth_legendrian_edge_rounding
-- name    : ContactTopology.smooth_legendrian_edge_rounding
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-31T01:27:28.107982+00:00
-- url     : https://prove2.me/theorems/c338639b-e2c6-4db4-bb1c-fde9c87c7170
-- title:
--   Smooth edge rounding and dividing-curve connection in the standard Legendrian collar
-- statement:
--   For every positive integer $n$ and scale $r>0$, consider the standard Legendrian-collar contact form on its real-coordinate cover,
--   $$\alpha_n=\sin(2\pi n z)\,dx+\cos(2\pi n z)\,dy.$$
--   Its coefficients are periodic in the longitudinal coordinate $z$ with period one. There exist a number $c>0$ and a globally smooth embedded strip $S:\mathbb R^2\to\mathbb R^3$, with injective derivative everywhere, which agrees exactly with the two flat faces outside the bend:
--   $$S(s,z)=(0,r(c-s),z)\quad(s\le0),\qquad S(s,z)=(r(c+s-1),0,z)\quad(s\ge1).$$
--   Thus the joins to the flat pieces are smooth to every order. The longitudinal rulings are Legendrian.
--
--   The affine radial field about $(rc,rc)$ is transverse to the whole strip. Its complete smooth flow is an actual family of diffeomorphisms and multiplies the contact form by $e^t$. The contact-volume coefficient of the model is exactly $2\pi n>0$.
--
--   There is a smooth phase function with $\psi(0)=0$ and $\psi(1)=\pi/2$ such that the dividing locus on the bent part is exactly
--   $$z=\frac{k}{2n}-\frac{\psi(s)}{2\pi n},\qquad k\in\mathbb Z,\quad 0\le s\le1.$$
--   Each branch has a globally smooth regular parametrization
--   $$\gamma_k(s)=S\!\left(s,\frac{k}{2n}-\frac{\psi(s)}{2\pi n}\right).$$
--   It joins the point $(0,rc,k/(2n))$ on the first face to $(rc,0,k/(2n)-1/(4n))$ on the second. This proves the quarter-turn connection of the dividing curves with a genuinely smooth rounding, rather than only tangent circular and flat pieces.
--
--   This is the explicit standard local model for edge rounding. It does not itself provide a compatible collar for arbitrary surfaces, descend the construction to a quotient manifold, construct a bypass disk, or prove a generic convex movie or the Legendrian-core classification.
-- source:
--   Ko Honda, Gluing tight contact structures, https://arxiv.org/abs/math/0102029, Section 1.5, edge-rounding discussion, arXiv p.11: standard collar form sin(2*pi*n*z) dx + cos(2*pi*n*z) dy and the dividing-curve connection shift -1/(4n). This is a constructed smooth model on the real-coordinate cover; the all-orders straight joins, complete affine contact flow, and exhaustive smooth dividing branches are derived details, not a verbatim general-manifold theorem.

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Order.IntermediateValue
open Set Function
open scoped ContDiff

theorem ContactTopology.smooth_legendrian_edge_rounding (n : ℕ) (hn : 0 < n)
    (r : ℝ) (hr : 0 < r) :
    let a : (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun y =>
      ![Real.sin (2*Real.pi*n*y 2),Real.cos (2*Real.pi*n*y 2),0]
    let α : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ := fun y v =>
      Real.sin (2*Real.pi*n*y 2)*v 0+Real.cos (2*Real.pi*n*y 2)*v 1
    ∃ c : ℝ, ∃ S : ℝ × ℝ → (Fin 3 → ℝ), ∃ X : (Fin 3 → ℝ) → (Fin 3 → ℝ),
    ∃ Φ : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ), ∃ phase : ℝ → ℝ,
    ∃ γ : ℤ → ℝ → (Fin 3 → ℝ),
      0 < c ∧ ContDiff ℝ ∞ S ∧ Topology.IsEmbedding S ∧
      (∀ p, Injective (fderiv ℝ S p)) ∧ ContDiff ℝ ∞ X ∧
      ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => Φ p.1 p.2) ∧
      ContDiff ℝ ∞ phase ∧ (∀ k, ContDiff ℝ ∞ (γ k)) ∧
      (∀ y, X y=![y 0-r*c,y 1-r*c,0]) ∧
      (∀ t y, Φ t y=![r*c+Real.exp t*(y 0-r*c),r*c+Real.exp t*(y 1-r*c),y 2]) ∧
      (∀ y, Φ 0 y=y) ∧ (∀ t y, Φ (-t) (Φ t y)=y) ∧
      (∀ t y, HasDerivAt (fun s => Φ s y) (X (Φ t y)) t) ∧
      (∀ t y v, α (Φ t y) (fderiv ℝ (Φ t) y v)=Real.exp t*α y v) ∧
      (∀ y,
        a y 0*(fderiv ℝ a y (Pi.single 1 1) 2-fderiv ℝ a y (Pi.single 2 1) 1)+
        a y 1*(fderiv ℝ a y (Pi.single 2 1) 0-fderiv ℝ a y (Pi.single 0 1) 2)+
        a y 2*(fderiv ℝ a y (Pi.single 0 1) 1-fderiv ℝ a y (Pi.single 1 1) 0)=2*Real.pi*n) ∧
      (∀ y v : Fin 3 → ℝ, α ![y 0,y 1,y 2+1] v=α y v) ∧
      (∀ s z, s ≤ 0 → S (s,z)=![0,r*(c-s),z]) ∧
      (∀ s z, 1 ≤ s → S (s,z)=![r*(c+s-1),0,z]) ∧
      (∀ p v : ℝ × ℝ, X (S p) ≠ fderiv ℝ S p v) ∧
      (∀ p : ℝ × ℝ, α (S p) (fderiv ℝ S p (0,1))=0) ∧
      phase 0=0 ∧ phase 1=Real.pi/2 ∧
      (∀ k s, γ k s=S (s,(k:ℝ)/(2*n)-phase s/(2*Real.pi*n))) ∧
      (∀ k s, deriv (γ k) s ≠ 0) ∧
      (∀ k, γ k 0=![0,r*c,(k:ℝ)/(2*n)] ∧
        γ k 1=![r*c,0,(k:ℝ)/(2*n)-1/(4*n)]) ∧
      ∀ s ∈ Icc (0:ℝ) 1, ∀ z : ℝ,
        (α (S (s,z)) (X (S (s,z)))=0 ↔
          ∃ k : ℤ, z=(k:ℝ)/(2*n)-phase s/(2*Real.pi*n)) := by sorry
