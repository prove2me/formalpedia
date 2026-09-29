-- Prove2me | Theorems.Thm_BraidsLinksMCG_fadellNeuwirth_ker_le_range
-- name    : BraidsLinksMCG.fadellNeuwirth_ker_le_range
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T19:52:00.622001+00:00
-- url     : https://prove2.me/theorems/142bee4a-e405-444a-8ecb-7b0d2e9d47d8
-- title:
--   Fadell--Neuwirth exactness: the kernel is contained in the image
-- statement:
--   The hard inclusion of exactness at the middle term of the Fadell--Neuwirth sequence: a pure braid on $n+1$ strands which becomes trivial after forgetting the last strand comes from a loop of that last strand alone in the plane punctured at the other $n$ points.
--
--   In symbols, for the sequence
--
--   $$\pi_1\bigl(E^{2}-Q_n\bigr) \longrightarrow \pi_1\bigl(F_{0,n+1}E^{2}\bigr) \longrightarrow \pi_1\bigl(F_{0,n}E^{2}\bigr),$$
--
--   with the first map induced by the fibre inclusion $\iota$ and the second by the forgetful map $p$, the claim is $\ker p_* \le \operatorname{im} \iota_*$.
--
--   The opposite inclusion is elementary and is already proved: the composite $p \circ \iota$ is the *constant* map at the base configuration, since forgetting the last coordinate of $(1, 2, \ldots, n, z)$ returns $(1, 2, \ldots, n)$ whatever $z$ is. So the composite induces the trivial homomorphism, and the image of $\iota_*$ lies in the kernel of $p_*$ for purely formal reasons. All the content of exactness is in the direction stated here.
--
--   The classical proof uses the homotopy lifting property. Given a loop $\gamma$ of configurations on $n+1$ points whose projection is null-homotopic, lift a null-homotopy of $p \circ \gamma$ through the fibration $F_{0,n+1}E^{2} \to F_{0,n}E^{2}$. The lifted homotopy deforms $\gamma$ into a loop lying entirely in a single fibre, and that fibre is the plane punctured at the $n$ fixed points, so the deformed loop is $\iota$ of a loop there.
--
--   This is where it is used that the Fadell--Neuwirth projection is a fibration. That input is not available from covering-space theory, which is what distinguishes this statement from the covering-space facts about the ordered-over-unordered projection.
-- source:
--   Birman, Braids, Links and Mapping Class Groups, Chapter 1, Theorem 1.4; Fadell and Neuwirth, Configuration spaces, Math. Scand. 10 (1962).

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace

namespace BraidsLinksMCG

theorem fadellNeuwirth_ker_le_range (n : ℕ) :
    (FundamentalGroup.mapOfEq (configForget n) (configForget_base n)).ker ≤
      (FundamentalGroup.mapOfEq (configIncl n) (configIncl_base n)).range := by sorry

end BraidsLinksMCG
