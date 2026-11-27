-- Prove2me | Theorems.Thm_ConjGrad_ErrorDecrease_Supplement_theorem_6_7
-- name    : ConjGrad.ErrorDecrease.Supplement.theorem_6_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T01:59:47.350673+00:00
-- url     : https://prove2.me/theorems/6017509d-70c3-4226-b46c-674deb088e3c
-- title:
--   Theorem 6:7 — the gradient of $f$ at $x_i$ in $\pi_i$ is a multiple of $p_i$
-- statement:
--   Let $x_i,p_i$ be the cg estimates and directions for a real symmetric positive definite $A$ with $Ah=k$, and $f(x)=(h-x,A(h-x))$. Let $\pi_i=x_i+W_i$ be the plane through $x_i$ conjugate to $p_0,\dots,p_{i-1}$, with $W_i=\{v:(Ap_j,v)=0,\ j<i\}$. The gradient of $f$ at $x_i$ in $\pi_i$ — the vector $g\in W_i$ with $Df(x_i)v=(g,v)$ for all $v\in W_i$ — is a scalar multiple of $p_i$: there is $c$ with $cp_i\in W_i$ and
--
--   $$Df(x_i)\,v=c\,(p_i,v)\qquad(v\in W_i).$$
--
--   This justifies the name of the method: each new direction is the gradient of the error function restricted to the plane conjugate to the previous directions.
--
--   **Formalization Note** Vectors are `Fin n → ℝ` with the dot product $(x,y)=\sum_l x_ly_l$ and $|z|^2=(z,z)$. The cg-method is the published iteration `cgIter` of (5:1), 0-based, with no stopping test: once $r_m=0$ Lean's convention $t/0=0$ keeps $x_i=h$ and $r_i=p_i=0$ for $i\ge m$. $A$ is real, symmetric and positive definite (`A.PosDef`), the paper's standing assumption on p. 410.
--
--   Differences from the source:
--   - generalization: statements about the run $x_0,\dots,x_m$ of the cg-method → the identities are asserted for every index $i$, including $i>m$ where Lean's $t/0=0$ gives $x_i=h$, $r_i=p_i=0$; reason: on $i\le m$ they are the source's statements; beyond $m$ both sides take the same totalized values
--   - reading: the gradient of $f$ at $x_i$ (the proof calls it $-r_i$) → the actual derivative `fderiv` of $f$, whose gradient is $-2r_i$; reason: the theorem asserts only proportionality, which a factor $2$ does not affect
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), DOI 10.6028/jres.049.044, p. 417, Theorem 6:7 (PDF p. 9)

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter
import Definitions.Def_ConjGrad_ErrorDecrease_errorFun
import Definitions.Def_ConjGrad_ErrorDecrease_Supplement_cdPlane

open Matrix

namespace ConjGrad.ErrorDecrease.Supplement

/-- Theorem 6:7 (Hestenes–Stiefel 1952, p. 417): the gradient of `f` at `xᵢ` in the plane `πᵢ`
(the vector of the direction space `conjDir A p i` of `πᵢ` representing the derivative of `f`
at `xᵢ` on that space) is a scalar multiple `c pᵢ` of `pᵢ`. -/
theorem theorem_6_7 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ h : Fin n → ℝ) (hh : A *ᵥ h = k) (i : ℕ) :
    ∃ c : ℝ, c • (cgIter A k x₀ i).p ∈ conjDir A (fun j => (cgIter A k x₀ j).p) i ∧
      ∀ v ∈ conjDir A (fun j => (cgIter A k x₀ j).p) i,
        fderiv ℝ (errorFun A h) (cgIter A k x₀ i).x v = c * ((cgIter A k x₀ i).p ⬝ᵥ v) := by sorry

end ConjGrad.ErrorDecrease.Supplement
