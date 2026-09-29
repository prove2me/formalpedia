-- Prove2me | Theorems.Thm_Coprimality_coprime_take_prod_drop_prod
-- name    : Coprimality.coprime_take_prod_drop_prod
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T18:02:31.616686+00:00
-- url     : https://prove2.me/theorems/b3db925d-d667-49ce-8d8a-b3fbf3d992f2
-- title:
--   Splitting a pairwise-coprime list gives coprime products
-- statement:
--   **Cutting a pairwise-coprime list anywhere yields two coprime products.**
--
--   If the entries of a list $l$ of naturals are pairwise coprime, then for every cut point $k$,
--
--   $$\gcd\Bigl(\prod_{i<k} l_i,\ \prod_{i\ge k} l_i\Bigr) \;=\; 1 .$$
--
--   Coprimality is multiplicative in each argument: if $a$ is coprime to each of $b_1,\dots,b_m$
--   then $a$ is coprime to their product. Applying this twice — first across the entries of the
--   suffix, then across those of the prefix — reduces the claim to pairwise coprimality of entries
--   on opposite sides of the cut, which is part of the hypothesis since `List.Pairwise` relates
--   every earlier entry to every later one.
--
--   The statement is the combinatorial engine behind Chinese-remainder constructions: to build an
--   integer with prescribed behaviour modulo several coprime moduli one repeatedly splits the list
--   of moduli and needs the two halves to remain coprime. It is also what justifies inducting over
--   a squarefree number's prime factorisation by peeling off an arbitrary initial segment.
--
--   **Formalization note.** `l.take k` and `l.drop k` are the prefix and suffix at the cut, and
--   `List.Pairwise Nat.Coprime` asserts coprimality of each earlier entry with each later one.
-- source:
--   Elementary. Lean proof extracted from `Salt/Maynard/` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace Coprimality

theorem coprime_take_prod_drop_prod {l : List ℕ} (h : l.Pairwise Nat.Coprime) (k : ℕ) :
    Nat.Coprime ((l.take k).prod) ((l.drop k).prod) := by sorry

end Coprimality
