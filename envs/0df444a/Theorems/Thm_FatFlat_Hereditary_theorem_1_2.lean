-- Prove2me | Theorems.Thm_FatFlat_Hereditary_theorem_1_2
-- name    : FatFlat.Hereditary.theorem_1_2
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-09T18:44:24.940476+00:00
-- url     : https://prove2.me/theorems/ef68be90-be51-42c9-853f-d6cccaf05f7d
-- title:
--   Theorem 1.2 — for hereditary classes: ISMF ⇔ FSMF ⇔ drill-flat ⇔ no large $K(r,k)$, $W(r,k)$
-- statement:
--   Let $\mathcal C$ be a hereditary class of finite simple graphs. The following four conditions are pairwise equivalent:
--   1. $\mathcal C$ is induced-shallow-minor-free: for every $d\in\mathbb N$ some graph $H_d$ is a $d$-shallow induced minor of no graph of $\mathcal C$;
--   2. $\mathcal C$ is fat-shallow-minor-free: there is an integer $\delta\ge1$ such that for every $\alpha\in\mathbb N$ some graph $H_\alpha$ is an $\alpha$-shallow $\delta$-fat minor of no graph of $\mathcal C$;
--   3. $\mathcal C$ is drill-flat: there is $\beta\ge1$ such that for every $\alpha\ge1$ there are $N:\mathbb N\to\mathbb N$ and $s\in\mathbb N$ such that every graph of $\mathcal C$ is $(\alpha,\beta)$-drill-flat with overhead $N$ and budget $s$;
--   4. for every $r\ge3$ there is $k\in\mathbb N$ such that no graph of $\mathcal C$ contains $K(r,k)$ or $W(r,k)$ as an induced subgraph.
--
--   Differences from the source:
--   - encoding: graph class (of finite simple graphs) → GraphClass: a predicate C V G on simple graphs G on finite vertex types V : Type; reason: a class of finite graphs; hereditary classes are closed under isomorphism, so the choice of vertex types does not matter
--   - reading: p. 3 gloss: δ ∈ N in FSMF, β ∈ N and every α ∈ N in drill-flat → Definitions 3.2–3.3 (p. 11): δ ≥ 1, β ≥ 1, α ≥ 1; reason: Part I states and proves the theorem for Definitions 3.1–3.3; the two readings give the same classes, since excluding a 0-fat minor implies excluding the 1-fat one, (α, Z)-scatteredness is monotone in Z (so β = 0 may be raised to 1), and α-scatteredness for α = 1 implies it for α = 0
-- source:
--   Filtser, Le, Mählmann, Ma. Pilipczuk, Mi. Pilipczuk, Fatness and Flatness, arXiv:2607.21474, Theorem 1.2, p. 3 (PDF p. 5); restated p. 10 (PDF 12); definitions p. 11 (PDF 13). Verbatim: 'Theorem 1.2. For every hereditary graph class C , the following are equivalent. (1) C is induced-shallow-minor-free. (2) C is fat-shallow-minor-free. (3) C is drill-flat. (4) For every r ⩾ 3 there is k ∈ N such that C excludes K(r, k) and W(r, k) as induced subgraphs.' PDF SHA-256: 757d7502abd8762f687daa2125d7908bd129bcf2f5d6d5cc1756b514302adaf1.

import Mathlib
import Definitions.Def_FatFlat_Hereditary_Basic
import Definitions.Def_FatFlat_Hereditary_Minors
import Definitions.Def_FatFlat_Hereditary_Patterns
import Definitions.Def_FatFlat_Hereditary_Classes

set_option autoImplicit false

namespace FatFlat.Hereditary

/-- **Theorem 1.2** (arXiv:2607.21474, p. 3, restated p. 10). For every hereditary graph class
`C`, the following are equivalent: (1) `C` is induced-shallow-minor-free; (2) `C` is
fat-shallow-minor-free; (3) `C` is drill-flat; (4) for every `r ≥ 3` there is `k ∈ ℕ` such
that `C` excludes `K(r, k)` and `W(r, k)` as induced subgraphs. -/
theorem theorem_1_2 (C : GraphClass) (hC : IsHereditary C) :
    List.TFAE [ISMF C, FSMF C, DrillFlat C, PatternFree C] := by sorry

end FatFlat.Hereditary
