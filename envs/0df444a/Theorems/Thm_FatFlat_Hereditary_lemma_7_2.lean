-- Prove2me | Theorems.Thm_FatFlat_Hereditary_lemma_7_2
-- name    : FatFlat.Hereditary.lemma_7_2
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-09T18:44:24.182853+00:00
-- url     : https://prove2.me/theorems/95147e1c-9017-447f-ab4e-b57765d9ca03
-- title:
--   Lemma 7.2 — boosting the subdivision parameter inside a hereditary class (both bullets)
-- statement:
--   For all natural numbers $r_{\mathrm{big}}\ge r_{\mathrm{small}}\ge3$ and every hereditary graph class $\mathcal C$:
--   - if $K(r_{\mathrm{small}},n)\in\mathcal C$ for every $n\in\mathbb N$, then there is $r_{\mathrm{bigger}}\ge r_{\mathrm{big}}$ with $K(r_{\mathrm{bigger}},n)\in\mathcal C$ for every $n\in\mathbb N$;
--   - if $W(r_{\mathrm{small}},n)\in\mathcal C$ for every $n\in\mathbb N$, then there is $r_{\mathrm{bigger}}\ge r_{\mathrm{big}}$ with $W(r_{\mathrm{bigger}},n)\in\mathcal C$ for every $n\in\mathbb N$.
--
--   Differences from the source:
--   - encoding: {K(r, n) | n ∈ N} ⊆ C → ∀ n, C _ (subdividedClique r n), membership of the concrete graph K(r, n); reason: a hereditary class is closed under isomorphism, so this is membership of K(r, n) up to isomorphism
-- source:
--   Filtser, Le, Mählmann, Ma. Pilipczuk, Mi. Pilipczuk, Fatness and Flatness, arXiv:2607.21474, Lemma 7.2, p. 21 (PDF p. 23). Verbatim: 'Lemma 7.2. For all naturals r_big ⩾ r_small ⩾ 3 and every hereditary graph class C: • If {K(r_small, n) | n ∈ N} ⊆ C, then also {K(r_bigger, n) | n ∈ N} ⊆ C, for some r_bigger ⩾ r_big. • If {W(r_small, n) | n ∈ N} ⊆ C, then also {W(r_bigger, n) | n ∈ N} ⊆ C, for some r_bigger ⩾ r_big.' PDF SHA-256: 757d7502abd8762f687daa2125d7908bd129bcf2f5d6d5cc1756b514302adaf1.

import Mathlib
import Definitions.Def_FatFlat_Hereditary_Basic
import Definitions.Def_FatFlat_Hereditary_Minors
import Definitions.Def_FatFlat_Hereditary_Patterns
import Definitions.Def_FatFlat_Hereditary_Classes

set_option autoImplicit false

namespace FatFlat.Hereditary

/-- **Lemma 7.2** (arXiv:2607.21474, p. 21). For all naturals `r_big ≥ r_small ≥ 3` and every
hereditary graph class `C`: if `K(r_small, n) ∈ C` for all `n`, then `K(r_bigger, n) ∈ C` for
all `n`, for some `r_bigger ≥ r_big`; and if `W(r_small, n) ∈ C` for all `n`, then
`W(r_bigger, n) ∈ C` for all `n`, for some `r_bigger ≥ r_big`. -/
theorem lemma_7_2 (rbig rsmall : ℕ) (hsmall : 3 ≤ rsmall) (hle : rsmall ≤ rbig)
    (C : GraphClass) (hC : IsHereditary C) :
    ((∀ n : ℕ, C _ (subdividedClique rsmall n)) →
      ∃ rbigger : ℕ, rbig ≤ rbigger ∧ ∀ n : ℕ, C _ (subdividedClique rbigger n)) ∧
    ((∀ n : ℕ, C _ (web rsmall n)) →
      ∃ rbigger : ℕ, rbig ≤ rbigger ∧ ∀ n : ℕ, C _ (web rbigger n)) := by sorry

end FatFlat.Hereditary
