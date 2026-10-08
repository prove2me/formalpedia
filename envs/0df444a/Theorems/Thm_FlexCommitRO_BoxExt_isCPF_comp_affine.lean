-- Prove2me | Theorems.Thm_FlexCommitRO_BoxExt_isCPF_comp_affine
-- name    : FlexCommitRO.BoxExt.isCPF_comp_affine
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:00:34.288729+00:00
-- url     : https://prove2.me/theorems/c71fe641-aadc-4d6a-8559-f5923f862368
-- title:
--   Proof of Lemma 2, p. 270 — an affine substitution of the variables preserves the c.p.f. property
-- statement:
--   Let $g : \mathbb R^k \to \mathbb R \cup \{+\infty\}$ be a convex polyhedral function, $M \in \mathbb R^{k \times m}$ and $v \in \mathbb R^k$. Then
--   $$
--   s \longmapsto g(Ms + v)
--   $$
--   is a convex polyhedral function on $\mathbb R^m$.
--
--   In the proof of Lemma 2 this makes $\Phi_T(s_T, d_T) = \operatorname{val}(B_{T+1}d_T + C_{T+1}s_T + b_{T+1})$ a c.p.f. in each argument.
-- source:
--   Ben-Tal, Golany, Nemirovski & Vial, Retailer-supplier flexible commitments contracts: a robust optimization approach, MSOM 7(3) (2005), p. 270, Appendix, proof of Lemma 2 ("an affine transformation of the variables … retain its c.p.f. property")

import Mathlib
import Definitions.Def_FlexCommitRO_BoxExt_WorstCaseDP
open Matrix

namespace FlexCommitRO.BoxExt

theorem isCPF_comp_affine {m k : ℕ} (g : (Fin k → ℝ) → EReal) (hg : IsCPF g)
    (M : Matrix (Fin k) (Fin m) ℝ) (v : Fin k → ℝ) :
    IsCPF (fun s : Fin m → ℝ => g (M *ᵥ s + v)) := by sorry

end FlexCommitRO.BoxExt
