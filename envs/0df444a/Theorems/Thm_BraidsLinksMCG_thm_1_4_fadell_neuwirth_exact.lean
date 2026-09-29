-- Prove2me | Theorems.Thm_BraidsLinksMCG_thm_1_4_fadell_neuwirth_exact
-- name    : BraidsLinksMCG.thm_1_4_fadell_neuwirth_exact
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T18:59:25.194448+00:00
-- url     : https://prove2.me/theorems/85ea05ac-3625-4869-a235-1ed7c24d1460
-- title:
--   Theorem 1.4: the Fadell–Neuwirth exact sequence for the plane
-- statement:
--   **Theorem 1.4 (for $M = E^2$).** Let $\pi : F_{0,n+1}E^2 \to F_{0,n}E^2$ be the projection
--   (1-4) deleting the last point, and let $j$ be the inclusion (1-6) of the punctured plane
--   $E^2 - \{1,\dots,n\}$ into $F_{0,n+1}E^2$ as the last coordinate, $z \mapsto (1,\dots,n,z)$.
--   Then the sequence
--
--   $$1 \longrightarrow \pi_1\bigl(E^2 - \{1,\dots,n\}\bigr)
--     \xrightarrow{\;j_*\;} \pi_1 F_{0,n+1}E^2
--     \xrightarrow{\;\pi_*\;} \pi_1 F_{0,n}E^2 \longrightarrow 1$$
--
--   is exact: $j_*$ is injective, $\pi_*$ is surjective, and the image of $j_*$ is the kernel of
--   $\pi_*$. Base points are the configuration $(1,2,\dots,k)$ in each configuration space and the
--   point $n+1$ in the punctured plane.
--
--   The plane satisfies the hypothesis of the general theorem, namely that the complement of a
--   finite point set has vanishing $\pi_0$, $\pi_2$ and $\pi_3$; the statement is indexed by $n+1$
--   rather than $n$ so that the projection is stated without truncated subtraction.
-- source:
--   Joan S. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82, Princeton University Press, 1974, Chapter 1, p. 14, Theorem 1.4 (sequence (1-7)), with the maps (1-4) and (1-6); specialized to $M = E^2$, which satisfies the hypothesis $\pi_2(M - Q_m) = \pi_3(M - Q_m) = \pi_0(M - Q_m) = 1$

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace

namespace BraidsLinksMCG

theorem thm_1_4_fadell_neuwirth_exact (n : ℕ) :
    Function.Injective (FundamentalGroup.mapOfEq (configIncl n) (configIncl_base n)) ∧
      Function.Surjective (FundamentalGroup.mapOfEq (configForget n) (configForget_base n)) ∧
      (FundamentalGroup.mapOfEq (configIncl n) (configIncl_base n)).range =
        (FundamentalGroup.mapOfEq (configForget n) (configForget_base n)).ker := by sorry

end BraidsLinksMCG
