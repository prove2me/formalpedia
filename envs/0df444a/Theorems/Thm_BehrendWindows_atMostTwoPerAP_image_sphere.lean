-- Prove2me | Theorems.Thm_BehrendWindows_atMostTwoPerAP_image_sphere
-- name    : BehrendWindows.atMostTwoPerAP_image_sphere
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-21T01:47:17.841043+00:00
-- url     : https://prove2.me/theorems/38f5b21a-8ba5-4ccf-a03b-a8caf02d367f
-- title:
--   Sphere images are $m$-sparse
-- statement:
--   Let $S,d,m,k\in\mathbb{N}$ with $d\ge 1$ and $m\ge 3$. Let $\Sigma_k$ be the set of vectors $x\in\{0,\dots,d-1\}^S$ with $\sum_i x_i^2=k$, and let
--
--   $$T=\Big\{\textstyle\sum_{i<S} x_i\,(md)^i\ :\ x\in\Sigma_k\Big\}\subset\mathbb{Z}.$$
--
--   Then $T$ is $m$-sparse (no $m$-term arithmetic progression with non-zero common difference contains three elements of $T$), and $T\subseteq\{0,1,\dots,(md)^S-1\}$.
--
--   **Formalization Note** $\Sigma_k$ is Mathlib's `Behrend.sphere S d k` and the digit map is `Behrend.map (m * d)`, cast to $\mathbb{Z}$.
-- source:
--   No published source states the version uniform in m; statement from the mission proposal, milestone 3; generalises Behrend.threeAPFree_sphere and F. A. Behrend, On sets of integers which contain no three terms in arithmetical progression, PNAS 32 (1946) 331-332, https://doi.org/10.1073/pnas.32.12.331

import Mathlib
import Definitions.Def_BehrendWindows_AtMostTwoPerAP

namespace BehrendWindows

theorem atMostTwoPerAP_image_sphere (S d m k : ℕ) (hd : 1 ≤ d) (hm : 3 ≤ m) :
    AtMostTwoPerAP ((Behrend.sphere S d k).image (fun x => (Behrend.map (m * d) x : ℤ))) m ∧
      (Behrend.sphere S d k).image (fun x => (Behrend.map (m * d) x : ℤ)) ⊆
        Finset.Ico (0 : ℤ) ((m * d) ^ S : ℕ) := by sorry

end BehrendWindows
