-- Prove2me | Theorems.Thm_Arxiv2507_18491_different_layers_direct_component
-- name    : Arxiv2507_18491.different_layers_direct_component
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-26T13:02:18.79428+00:00
-- url     : https://prove2.me/theorems/d4cb68c0-64b7-5895-9169-8780d40d235d
-- title:
--   Section 3.2: in different layers exactly one component has transmission distance $|z-z'|$
-- statement:
--   Let the interfaces satisfy $d_0>\dots>d_{L-1}$, and let the target height $z$ lie in layer $\ell$ and the source height $z'$ lie in layer $\ell'\neq\ell$.
--
--   1. If $\ell<\ell'$, the component $\uparrow\uparrow$ has vertical transmission distance exactly $|z-z'|$, and every other defined component has a strictly larger one.
--   2. If $\ell>\ell'$, the same holds for the component $\downarrow\downarrow$.
--
--   **Formalization Note** The paper's further assertion that this component is nonzero ("it must exist") depends on the densities, which the paper does not give, and is not formalized.
-- source:
--   Yuan, Wang, Zhang and Cai, Fast multipole method for Maxwell's equations in layered media, arXiv:2507.18491v1 (2025), claim c007; Section 3.2, text on Figs. 3.2-3.3, with eqs. (3.21), (3.22), (3.24), PDF p. 11

import Mathlib
import Definitions.Def_Arxiv2507_18491_Basic

open MeasureTheory Filter Topology

namespace Arxiv2507_18491

theorem different_layers_direct_component (L : ℕ) (d : ℕ → ℝ) (hd : IsInterfaces L d)
    (l l' : ℕ) (hll : l ≠ l') (z z' : ℝ) (hz : InLayer L d l z) (hz' : InLayer L d l' z') :
    (l < l' → CompDefined L l l' true true ∧ vertDist d l l' true true z z' = |z - z'| ∧
      ∀ a b : Dir, CompDefined L l l' a b → ¬(a = true ∧ b = true) →
        |z - z'| < vertDist d l l' a b z z') ∧
    (l' < l → CompDefined L l l' false false ∧ vertDist d l l' false false z z' = |z - z'| ∧
      ∀ a b : Dir, CompDefined L l l' a b → ¬(a = false ∧ b = false) →
        |z - z'| < vertDist d l l' a b z z') := by sorry

end Arxiv2507_18491
