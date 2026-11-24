-- Prove2me | Theorems.Thm_ConjGrad_ErrorDecrease_Supplement_theorem_4_6
-- name    : ConjGrad.ErrorDecrease.Supplement.theorem_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:55:06.425275+00:00
-- url     : https://prove2.me/theorems/4a67da2f-f70e-42b7-b1d3-84415d236208
-- title:
--   Theorem 4:6 — the planes $\pi_i$, the ellipsoids $E_i'$ centred at $h$, and the chords $C_i$
-- statement:
--   Let $A$ be real symmetric positive definite, $Ah=k$, $f(x)=(h-x,A(h-x))$. For a run of the cd-method and a step $i$, let $\pi_i=x_i+W_i$ be the plane through $x_i$ conjugate to $p_0,\dots,p_{i-1}$, where $W_i=\{v:(Ap_j,v)=0,\ j<i\}$. Then
--
--   1. $\pi_i$ is $(n-i)$-dimensional when $p_0,\dots,p_{i-1}$ are nonzero: $\dim W_i=n-i$;
--   2. $\pi_i$ contains $x_i,x_{i+1},\dots$ and $h$;
--   3. its intersection $E_i'$ with the level set $f(x)=f(x_i)$ is
--   $$E_i'=\{\,h+v:\ v\in W_i,\ (v,Av)=f(x_i)\,\},$$
--   an ellipsoid of dimension $n-i-1$ in $\pi_i$ with centre $h$ (the single point $h$ when $f(x_i)=0$);
--   4. $x_{i+1}$ is the midpoint of the chord $C_i$ of $E_i'$ through $x_i$ parallel to $p_i$: the point $2x_{i+1}-x_i$ lies on the line $x_i+tp_i$ and on $E_i'$, and $x_i$ and $2x_{i+1}-x_i$ are the only points of that line on $E_i'$.
--
--   For the cg-method, moreover, the chord $C_i$ is normal to $E_i'$ at $x_i$: $p_i\in W_i$ and $p_i$ is orthogonal to every $v\in W_i$ with $Df(x_i)v=0$; hence it is in the direction of the gradient of $f$ at $x_i$ in $\pi_i$: $Df(x_i)v=c\,(p_i,v)$ for all $v\in W_i$ and some scalar $c$.
--
--   The theorem is the geometric picture of the cd- and cg-methods: each step halves a chord of a nested family of ellipsoids centred at the solution, and in the cg-method the chord is the restricted gradient direction.
--
--   **Formalization Note** Vectors are `Fin n → ℝ`. The cd-run is any `IsCDRun`; the cg-run is the published `cgIter` (5:1). `conjDir A p i` is $W_i$ and `conjPlane A p (x i) i` is $\pi_i$. The derivative is `fderiv ℝ (errorFun A h)`; the gradient itself is $-2r_i$.
--
--   Differences from the source:
--   - generalization: a cd-method, whose formula (4:1a) is defined for nonzero directions → every run satisfying `IsCDRun`, a zero direction giving step $a_i=0/0=0$; reason: for runs with nonzero directions it is exactly the source's statement
--   - reading: $E_i'$ is an ellipsoid of dimension $n-i-1$ with centre $h$ → $h\in\pi_i$ and $E_i'=\{h+v: v\in W_i,\ (v,Av)=f(x_i)\}$ with $\dim W_i=n-i$; reason: this is the explicit description of an ellipsoid of the stated dimension centred at $h$; it also covers the degenerate level $f(x_i)=0$ (the point $h$) and a tangent chord with $x_{i+1}=x_i$, both of which the source allows
--   - reading: the gradient of $f$ at $x_i$ in $\pi_i$ → the derivative $Df(x_i)$ restricted to $W_i$, represented by a multiple of $p_i\in W_i$; reason: a gradient in a plane is the vector of the plane representing the derivative on it; no factor convention enters
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), DOI 10.6028/jres.049.044, p. 414, Theorem 4:6 (PDF p. 6)

import Mathlib
import Definitions.Def_ConjGrad_Termination_IsCDRun
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter
import Definitions.Def_ConjGrad_ErrorDecrease_errorFun
import Definitions.Def_ConjGrad_ErrorDecrease_Supplement_cdPlane

open Matrix

namespace ConjGrad.ErrorDecrease.Supplement

/-- Theorem 4:6 (Hestenes–Stiefel 1952, p. 414). First part: every run of the cd-method.
`conjPlane A p (x i) i` is the plane `πᵢ` through `xᵢ` conjugate to `p₀, …, pᵢ₋₁`, with
direction space `conjDir A p i`; `Eᵢ'` is its intersection with the level set
`f(x) = f(xᵢ)`. Second part: the cg-method. -/
theorem theorem_4_6 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k h : Fin n → ℝ) (hh : A *ᵥ h = k) :
    (∀ (x r p : ℕ → Fin n → ℝ), Termination.IsCDRun A k x r p → ∀ i : ℕ,
      ((∀ j < i, p j ≠ 0) → Module.finrank ℝ (conjDir A p i) = n - i) ∧
      (∀ j, i ≤ j → x j ∈ conjPlane A p (x i) i) ∧
      h ∈ conjPlane A p (x i) i ∧
      {y | y ∈ conjPlane A p (x i) i ∧ errorFun A h y = errorFun A h (x i)} =
        {y | ∃ v ∈ conjDir A p i, y = h + v ∧ v ⬝ᵥ (A *ᵥ v) = errorFun A h (x i)} ∧
      ((2 : ℝ) • x (i + 1) - x i ∈ conjPlane A p (x i) i ∧
        errorFun A h ((2 : ℝ) • x (i + 1) - x i) = errorFun A h (x i)) ∧
      (∃ t : ℝ, (2 : ℝ) • x (i + 1) - x i = x i + t • p i) ∧
      (∀ t : ℝ, x i + t • p i ∈ conjPlane A p (x i) i →
        errorFun A h (x i + t • p i) = errorFun A h (x i) →
        x i + t • p i = x i ∨ x i + t • p i = (2 : ℝ) • x (i + 1) - x i)) ∧
    (∀ (x₀ : Fin n → ℝ) (i : ℕ),
      (cgIter A k x₀ i).p ∈ conjDir A (fun j => (cgIter A k x₀ j).p) i ∧
      (∀ v ∈ conjDir A (fun j => (cgIter A k x₀ j).p) i,
        fderiv ℝ (errorFun A h) (cgIter A k x₀ i).x v = 0 → (cgIter A k x₀ i).p ⬝ᵥ v = 0) ∧
      ∃ c : ℝ, ∀ v ∈ conjDir A (fun j => (cgIter A k x₀ j).p) i,
        fderiv ℝ (errorFun A h) (cgIter A k x₀ i).x v = c * ((cgIter A k x₀ i).p ⬝ᵥ v)) := by sorry

end ConjGrad.ErrorDecrease.Supplement
