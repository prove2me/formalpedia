-- Prove2me | Theorems.Thm_BlockSSM_Supplement_theorem_15
-- name    : BlockSSM.Supplement.theorem_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:07:39.320737+00:00
-- url     : https://prove2.me/theorems/e1ea8383-3858-4781-8a88-f0eee645fa2e
-- title:
--   Theorem 15 — subspace-cover profiles, $D_b(G_{p,r})=\tau_b(r)$
-- statement:
--   Let $r\ge2$ and let $p$ be a prime with $p>2^r$. Then
--   1. $D_b(G_{p,r})=\tau_b(r)$ for every block bound $b$ (including $b=\infty$);
--   2. $w^{\twoheadrightarrow}(G_{p,r})=2$;
--   3. $D_\infty(G_{p,r})=2^r$.
--
--   Here $G_{p,r}=\bigl(\bigoplus_{0\neq\chi\in\widehat Q}A_\chi\bigr)\rtimes Q$ with $Q=C_2^r$, $\tau_b(r)$ is the least total size of a cover of $\widehat Q\cong\mathbb F_2^r$ by subspaces of size at most $b$, and $w^{\twoheadrightarrow}$ is the covering width.
--
--   These groups show that block size remains a quantitative resource after feasibility: the profile $b\mapsto D_b(G_{p,r})$ keeps decreasing.
--
--   Differences from the source:
--   - encoding: $Q=C_2^r$, $\widehat Q\cong\mathbb F_2^r$, $\chi(q)$, $G_{p,r}$ → `Gpr p r`: $\mathbb F_2^r$ and the function space on nonzero characters, written multiplicatively, with $\chi(q)=(-1)^{\chi\cdot q}$ and Mathlib's semidirect product; reason: the same group, with the identification the paper fixes
--   - encoding: $\tau_b(r)$ and $w^{\twoheadrightarrow}$ → infima in `ℕ∞` over finite families (`tau`, `coveringWidth`); reason: for a finite group and the finite space $\widehat Q$ finite families suffice; `sInf ∅ = ⊤`
--   - generalization: $D_b$ for every block bound $b\ge1$, and $D_\infty$ → every $b\in$ `ℕ∞` ($b=0$ included), and $b=$ `⊤`; reason: $D_\infty$ is the unbounded case of Definition 2; at the extra instance $b=0$ both sides are $\infty$ (no subspace has size $0$; no nonzero representation has irreducible degrees $\le0$); every source instance is a case
--   - encoding: finite covers $H$ and representations $V$ in $D_b$ → $H$ in the lowest universe, $V=\mathbb C^d$ (published `BlockSSM.coverDim`); reason: every finite group has an isomorphic copy in `Type` and every $d$-dimensional representation is isomorphic to one on $\mathbb C^d$
-- source:
--   C. Geng, The State Complexity of Block-Diagonal State Space Models, STOC 2027 submission manuscript (sha256 f9071794…), Theorem 15, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_BlockSSM_coverDim
import Definitions.Def_BlockSSM_Supplement_Gpr
import Definitions.Def_BlockSSM_Supplement_tau
import Definitions.Def_BlockSSM_Supplement_coveringWidth

namespace BlockSSM.Supplement

open BlockSSM

/-- **Theorem 15 (subspace-cover profiles).** Geng, *The State Complexity of Block-Diagonal State Space Models*, STOC 2027 submission manuscript (sha256 f9071794…), Theorem 15, p.7 (PDF p.8): "D_b(G_{p,r}) = τ_b(r)
for r ≥ 2 and prime p > 2^r. In particular w↠(G_{p,r}) = 2 and D_∞(G_{p,r}) = 2^r."

**Formalization Note.** All three conclusions are stated: the equality for every `b : ℕ∞`
(`b = ∞` included), the covering width `w↠` of Definition 2 (`coveringWidth`), and the value at
`b = ⊤`. `2 ^ r` is two to the power `r`. -/
theorem theorem_15 (p r : ℕ) (hp : p.Prime) (hr : 2 ≤ r) (hpr : 2 ^ r < p) :
    (∀ b : ℕ∞, coverDim (Gpr p r) b = tau r b) ∧ coveringWidth (Gpr p r) = 2 ∧
      coverDim (Gpr p r) ⊤ = ((2 ^ r : ℕ) : ℕ∞) := by sorry

end BlockSSM.Supplement
