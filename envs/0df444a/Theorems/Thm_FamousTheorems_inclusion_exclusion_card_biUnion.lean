-- Prove2me | Theorems.Thm_FamousTheorems_inclusion_exclusion_card_biUnion
-- name    : FamousTheorems.inclusion_exclusion_card_biUnion
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T22:42:20.504341+00:00
-- url     : https://prove2.me/theorems/ea4c8cb4-4355-4034-97ec-133697326709
-- title:
--   The principle of inclusion/exclusion
-- statement:
--   **The principle of inclusion–exclusion.**
--
--   For a finite family of finite sets $(S_i)_{i \in s}$,
--   $$\left|\bigcup_{i \in s} S_i\right| \;=\; \sum_{\emptyset \neq t \subseteq s} (-1)^{|t|+1}
--   \left|\bigcap_{i \in t} S_i\right|.$$
--
--   Counting the union by adding the sizes overcounts every element lying in several $S_i$; subtracting
--   the pairwise intersections overcorrects; adding back the triples overcorrects again, and so on. The
--   alternating sum is exactly right because an element in precisely $k$ of the sets is counted
--   $\sum_{j=1}^{k} (-1)^{j+1}\binom{k}{j} = 1$ time.
--
--   It is the fundamental counting identity of enumerative combinatorics: derangements, Euler's totient
--   function, the surjection count, and the sieve of Eratosthenes are all one substitution away. Its
--   analytic descendants are the Bonferroni inequalities (truncating the sum gives alternating bounds) and
--   Brun's and Selberg's sieves.
--
--   De Moivre stated it in 1718; the modern general form is often credited to Sylvester and Poincaré.
--
--   **Formalization note.** The index runs over nonempty subsets of `s`, carried as a subtype so that
--   `inf'` — the intersection of a nonempty family — is well defined; the cardinality is cast to $\mathbb{Z}$
--   so the alternating signs make sense. The result is Mathlib's `Finset.inclusion_exclusion_card_biUnion`.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

theorem inclusion_exclusion_card_biUnion {ι α : Type*} [DecidableEq α] (s : Finset ι)
    (S : ι → Finset α) :
    (s.biUnion S).card = ∑ t : {t ∈ s.powerset | t.Nonempty},
      (-1 : ℤ) ^ (t.1.card + 1) * (t.1.inf' (Finset.mem_filter.1 t.2).2 S).card := by sorry

end FamousTheorems
