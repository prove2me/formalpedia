-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsC_mnat_convex_local_representation
-- name    : DiscreteConvex.MConvexFunctionsC.mnat_convex_local_representation
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-29T03:01:46.529122+00:00
-- url     : https://prove2.me/theorems/6e940299-eb60-40e1-aa2b-c8a7862d9463
-- title:
--   Constructive localization of convex combinations for M♮-convex functions
-- statement:
--   Let $V$ be finite and let $f:\mathbb Z^V\to\mathbb R\cup\{+\infty\}$ be M♮-convex. Suppose a finite convex combination of effective-domain points has mean $p$:
--
--   $$
--   \lambda_y\ge0,\qquad \sum_{y\in S}\lambda_y=1,\qquad \sum_{y\in S}\lambda_y y=p.
--   $$
--
--   There is a convex combination on $T=N(p)\cap\operatorname{dom}f$, where $N(p)=[\lfloor p\rfloor,\lceil p\rceil]\cap\mathbb Z^V$, with the same mean and no greater cost:
--
--   $$
--   \mu_y\ge0,\qquad \sum_{y\in T}\mu_y=1,\qquad \sum_{y\in T}\mu_y y=p,\qquad
--   \sum_{y\in T}\mu_y f(y)\le\sum_{y\in S}\lambda_y f(y).
--   $$
--
--   This exposes the constructive localization lemma already proved inside the accepted proof of Theorem 6.42, so that subsequent convex-combination arguments can import its actual weights rather than repeat that proof. It is not a new mathematical claim.
-- source:
--   Constructive lemma local_le in the accepted proof of DiscreteConvex.MConvexFunctionsC.mnat_convex_integrally_convex by mrfancypants, https://prove2.me/submissions/5ac997fe-8d9b-4700-910b-9f1a12aaa4d9 . Underlying source: K. Murota, Discrete Convex Analysis, SIAM 2003, p.159, Theorem 6.42. The proof here is extracted and credited from that accepted submission.

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MNaturalConvex
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_ConvexExtensible
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_IsIntegrallyConvexFunction
open DiscreteConvex.MConvexFunctionsC
open Classical

theorem DiscreteConvex.MConvexFunctionsC.mnat_convex_local_representation {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ) (hf : MNaturalConvex f) (p : V → ℝ)
    (S : Finset (V → ℤ)) (hS : ∀ y ∈ S, y ∈ DomZ f)
    (lam : (V → ℤ) → ℝ) (h0 : ∀ y ∈ S, 0 ≤ lam y) (h1 : ∑ y ∈ S, lam y = 1)
    (h2 : ∀ v, ∑ y ∈ S, lam y * (y v : ℝ) = p v) :
    ∃ lam' : (V → ℤ) → ℝ,
      (∀ y ∈ Finset.filter (fun y => y ∈ DomZ f) (IntegralNeighborhoodFinset p), 0 ≤ lam' y) ∧
      (∑ y ∈ Finset.filter (fun y => y ∈ DomZ f) (IntegralNeighborhoodFinset p), lam' y = 1) ∧
      (∀ v, ∑ y ∈ Finset.filter (fun y => y ∈ DomZ f) (IntegralNeighborhoodFinset p),
        lam' y * (y v : ℝ) = p v) ∧
      ∑ y ∈ Finset.filter (fun y => y ∈ DomZ f) (IntegralNeighborhoodFinset p),
        lam' y * (f y).untopD 0 ≤ ∑ y ∈ S, lam y * (f y).untopD 0 := by sorry
