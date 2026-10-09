-- Prove2me | Theorems.Thm_AffineVolterra_RiccatiSqrt_lemma_C_1
-- name    : AffineVolterra.RiccatiSqrt.lemma_C_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:50:28.277166+00:00
-- url     : https://prove2.me/theorems/718c26e2-55c1-4864-8bf3-a64e7ccadf0f
-- title:
--   Lemma C.1, p. 42 — linear Volterra solvability and L² stability
-- statement:
--   On a finite interval $[0,T]$, let $G$ be a square integrable complex matrix function, and let $F^n$ and $K^n$ be square integrable vector and matrix functions. For each $n$, there is a unique square integrable vector solution of
--   $$
--   \chi^n=F^n+K^n*(G\chi^n).
--   $$
--   If $F^n\to F^0$ and $K^n\to K^0$ in $L^2(0,T)$, then $\chi^n\to\chi^0$ in $L^2(0,T)$. This gives both existence for linear convolution equations and stability under approximating the kernel.
--
--   **Formalization Note** The page prints $\chi^n\in L^2([0,T],\mathbb C^{d\times d})$, though the equation is vector valued; Lean uses $\mathbb C^d$. The page's unused $u\in\mathbb C^d$ is omitted. Matrix $L^2$ convergence is componentwise, equivalent in finite dimension to operator-norm convergence.
-- source:
--   Abi Jaber, Larsson and Pulido, Affine Volterra processes, arXiv:1708.08796v3, Lemma C.1, p. 42

import Mathlib
import Definitions.Def_AffineVolterra_RiccatiSqrt_Setting

namespace AffineVolterra.RiccatiSqrt

open MeasureTheory Filter

/-- Lemma C.1, p. 42; the printed codomain of χⁿ is corrected to ℂᵈ. -/
theorem lemma_C_1 {d : ℕ} (T : ℝ) (hT : 0 ≤ T)
    (G : ℝ → CMat d) (F : ℕ → ℝ → AffineVolterra.Transform.CVec d) (K : ℕ → ℝ → CMat d)
    (hG : ∀ i j, MemLp (fun t => G t i j) 2 (volume.restrict (Set.Ioc 0 T)))
    (hF : ∀ n, MemLp (F n) 2 (volume.restrict (Set.Ioc 0 T)))
    (hK : ∀ n i j, MemLp (fun t => K n t i j) 2 (volume.restrict (Set.Ioc 0 T))) :
    ∃ χ : ℕ → ℝ → AffineVolterra.Transform.CVec d,
      (∀ n, SolvesOn (K n) (F n) (fun t x => mulVec (G t) x) (χ n) T) ∧
      (∀ n φ, SolvesOn (K n) (F n) (fun t x => mulVec (G t) x) φ T →
        φ =ᵐ[volume.restrict (Set.Ioc 0 T)] χ n) ∧
      ((Tendsto (fun n => eLpNorm (fun t => F n t - F 0 t) 2
          (volume.restrict (Set.Ioc 0 T))) atTop (nhds (0 : ENNReal)) ∧
        ∀ i j, Tendsto (fun n => eLpNorm (fun t => K n t i j - K 0 t i j) 2
          (volume.restrict (Set.Ioc 0 T))) atTop (nhds (0 : ENNReal))) →
        Tendsto (fun n => eLpNorm (fun t => χ n t - χ 0 t) 2
          (volume.restrict (Set.Ioc 0 T))) atTop (nhds (0 : ENNReal))) := by sorry

end AffineVolterra.RiccatiSqrt
