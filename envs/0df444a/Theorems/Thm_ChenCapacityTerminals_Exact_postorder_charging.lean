-- Prove2me | Theorems.Thm_ChenCapacityTerminals_Exact_postorder_charging
-- name    : ChenCapacityTerminals.Exact.postorder_charging
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T06:47:07.423577+00:00
-- url     : https://prove2.me/theorems/5e398ffb-3dca-4bb6-a0d7-ee08c7b604f2
-- title:
--   Theorem 2.1 — guide postorder, marked-mass charging and surviving components
-- statement:
--   For every legal construction, the returned terminal set lies in $V\setminus\{r\}$. The strict postorder marks, after deleting $r$ and the dummy root, number at most $b(V)/(t+1)$: each mark kills a disjoint integral-mass portion of size at least $t+1$, the dummy has mass zero, and deleting $r$ can only help. Moreover, if $X$ avoids all marks and $r$, then every weak component of the guide induced by $X$ has mass at most $t$. Each component has an entering guide edge, giving
--   $$b(X)\le t\,\operatorname{guideEntries}(\operatorname{guide},X).$$
--   This is the tree/postorder argument of Theorem 2.1, independent of the cut-capacity charging in Lemma 2.3. Empty $X$ and disconnected guides are included.
-- source:
--   Thomas Chen, STOC 2027 submission #665 (October 2026), Theorem 2.1 and §2.3 “Weighted separation and implementation”, pp. 3–5, PDF pp. 4–7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/665.pdf#page=7

import Definitions.Def_ChenCapacityTerminals_Exact_Specifications

set_option autoImplicit false

open ChenCapacityTerminals.Exact

theorem ChenCapacityTerminals.Exact.postorder_charging
    (G : Network) (r d : ℕ) (L : ℚ) (b : ℕ → ℕ) (t : ℕ) (c : Construction)
    (hc : LegalConstruction G r d L b t c) :
    c.terminals G r ((L : ℝ) / (4 * d)) b t ⊆ G.vertices \ {r} ∧
    ((c.marks G ((L : ℝ) / (4 * d)) b t \ {r, dummy G}).card : ℝ) ≤
      (mass b G.vertices : ℝ) / (t + 1 : ℕ) ∧
    ∀ X ⊆ G.vertices \ (c.marks G ((L : ℝ) / (4 * d)) b t ∪ {r}),
      (mass b X : ℝ) ≤ (t : ℝ) * (guideEntries (c.guide G ((L : ℝ) / (4 * d))) X : ℝ) := by sorry
