-- Prove2me | Theorems.Thm_BSPConvex_CMM_epigraph_g
-- name    : BSPConvex.CMM.epigraph_g
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:52.313471+00:00
-- url     : https://prove2.me/theorems/d630cf8c-5fff-4fd8-b229-131f29b02a73
-- title:
--   Proof of Theorem 2, p. 28 — the epigraph of g as a linear matrix inequality, lifted to three constraints
-- statement:
--   Let $\Sigma\succ 0$, $q\in\operatorname{int}(\Delta_m)$ and $t\in\mathbb R$. Write $\tau=\operatorname{tr}(T(q)^{1/2})$ and $M(q)=\Sigma^{1/2}(T(q))^{-1/2}\Sigma^{1/2}$. The following are equivalent:
--
--   1. $g(q)\le\tfrac12 t$;
--   2. $t+\tau-q^\top M(q)q\ge 0$;
--   3. $$\begin{pmatrix} t+\tau & q^\top\Sigma^{1/2}\\ \Sigma^{1/2}q & T(q)^{1/2}\end{pmatrix}\succeq 0;$$
--   4. there are $z\in\mathbb R$ and an $m\times m$ matrix $Z$ with
--   $$\begin{pmatrix} z & q^\top\Sigma^{1/2}\\ \Sigma^{1/2}q & Z\end{pmatrix}\succeq 0,\qquad t+\tau\ge z,\qquad T(q)^{1/2}\succeq Z.$$
--
--   This is the description of the epigraph $\{(q,t): g(q)\le\tfrac12t\}$ in the proof of Theorem 2: the epigraph is represented by three constraints, each of which is then shown to be convex.
--
--   **Formalization Note** The formal statement is the three consecutive equivalences 1⇔2, 2⇔3, 3⇔4 at a fixed $(q,t)$, which is the paper's chain of set equalities. The block matrix is indexed by `Unit ⊕ Fin m`; its top-right row is $q^\top\Sigma^{1/2}$ (`q ᵥ* CFC.sqrt Sig`) and its bottom-left column $\Sigma^{1/2}q$, as printed. The condition $T(q)^{1/2}\succeq Z$ is `(CFC.sqrt (T q) - Z).PosSemidef`, which forces $Z$ to be symmetric, as for a matrix variable in a linear matrix inequality. The domain is $\operatorname{int}(\Delta_m)$ because $(T(q))^{-1/2}$ occurs.
-- source:
--   Li, Sun & Teo, Convex Optimization for Bundle Size Pricing Problem, SSRN 3426933 (version of May 8, 2021), p. 28, proof of Theorem 2 (epigraph of g)

import Mathlib
import Definitions.Def_BSPConvex_CMM_Model

open Matrix
open scoped MatrixOrder

namespace BSPConvex.CMM

theorem epigraph_g {m : ℕ} (Sig : Matrix (Fin m) (Fin m) ℝ) (hSig : Sig.PosDef)
    (q : Fin m → ℝ) (hq : q ∈ intSimplex m) (t : ℝ) :
    (gFun Sig q ≤ (1 / 2 : ℝ) * t ↔
        t + Matrix.trace (CFC.sqrt (Tmat Sig q)) - q ⬝ᵥ (Mmat Sig q *ᵥ q) ≥ 0) ∧
      (t + Matrix.trace (CFC.sqrt (Tmat Sig q)) - q ⬝ᵥ (Mmat Sig q *ᵥ q) ≥ 0 ↔
        (bord (t + Matrix.trace (CFC.sqrt (Tmat Sig q))) (q ᵥ* CFC.sqrt Sig) (CFC.sqrt Sig *ᵥ q)
          (CFC.sqrt (Tmat Sig q))).PosSemidef) ∧
      ((bord (t + Matrix.trace (CFC.sqrt (Tmat Sig q))) (q ᵥ* CFC.sqrt Sig) (CFC.sqrt Sig *ᵥ q)
          (CFC.sqrt (Tmat Sig q))).PosSemidef ↔
        ∃ (z : ℝ) (Z : Matrix (Fin m) (Fin m) ℝ),
          (bord z (q ᵥ* CFC.sqrt Sig) (CFC.sqrt Sig *ᵥ q) Z).PosSemidef ∧
            t + Matrix.trace (CFC.sqrt (Tmat Sig q)) ≥ z ∧
            (CFC.sqrt (Tmat Sig q) - Z).PosSemidef) := by sorry

end BSPConvex.CMM
