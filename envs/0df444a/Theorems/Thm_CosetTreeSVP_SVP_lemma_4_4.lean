-- Prove2me | Theorems.Thm_CosetTreeSVP_SVP_lemma_4_4
-- name    : CosetTreeSVP.SVP.lemma_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:33:25.316862+00:00
-- url     : https://prove2.me/theorems/e91ce9c3-b967-4042-bb05-3ca4fbe471b2
-- title:
--   Lemma 4.4 — Parseval over the uniform δ: E_δ‖Σ_α χ_α(δ)B_α‖² = Σ_α ‖B_α‖²
-- statement:
--   Let $q$ be prime, $\mathbb F_q^n = H_1\oplus\cdots\oplus H_m$ the coordinate decomposition, and index families $\alpha = (\alpha_{j,a})$, $\delta = (\delta_{j,a})$ by $j \in [m-1]$, $a \in [0, p/2^j)$ with $\alpha_{j,a}, \delta_{j,a} \in H_j$.
--
--   **Lemma 4.4.** For vectors $B_\alpha \in \mathbb C^n$ and $\chi_\alpha(\delta) = \prod_{j=1}^{m-1}\prod_{a=0}^{p/2^j-1}\omega_q^{-\langle\alpha_{j,a},\delta_{j,a}\rangle}$, with $\delta$ uniform,
--   $$\mathbb E_\delta\Big[\Big\|\sum_\alpha\chi_\alpha(\delta)B_\alpha\Big\|^2\Big] = \sum_\alpha\|B_\alpha\|^2.\tag{30}$$
--   It converts the bound of Lemma 4.5 into a bound on the error of $A_\delta(\theta^*)$.
--
--   Differences from the source:
--   - generalization: p, m, q of Eq. (17), m | n → every n, p, m and every prime q, with footnote 7's blocks; reason: character orthogonality holds for every choice; it specializes to the paper's parameters
--   - encoding: E_δ → the average over the finite type of families with δ_{j,a} ∈ H_j; reason: δ_{j,a} independent and uniform
-- source:
--   Hhan, Finding a Shortest Vector and More in 2^{n/2+o(n)} Time using q-ary Coset Difference Tree, arXiv:2609.02764 (held version, sha256 687602f4…), p. 18 (PDF 20), Lemma 4.4

import Mathlib
import Definitions.Def_SuperlatSVP_lat
import Definitions.Def_RegevLWE_GaussConv_Lattice
import Definitions.Def_RegevLWE_Hyperplane_DiscreteGaussian
import Definitions.Def_CosetTreeSVP_SVP_Basics
import Definitions.Def_CosetTreeSVP_SVP_Tree

open MeasureTheory Filter Topology
open scoped ENNReal

namespace CosetTreeSVP.SVP

theorem lemma_4_4 (n p m q : ℕ) [NeZero q] (hq : q.Prime) (Bα : Fam n p m q → CE n) :
    ∑ δ : Fam n p m q, (Fintype.card (Fam n p m q) : ℝ)⁻¹ *
        ‖∑ α : Fam n p m q,
          (∏ ia : TIdx p m, omegaPow q (-(dotq (α ia).val (δ ia).val))) • Bα α‖ ^ 2 =
      ∑ α : Fam n p m q, ‖Bα α‖ ^ 2 := by sorry

end CosetTreeSVP.SVP
