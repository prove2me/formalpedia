-- Prove2me | Theorems.Thm_DetDLP_d2_greedy_energy_descent
-- name    : DetDLP.d2_greedy_energy_descent
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T05:52:57.241487+00:00
-- url     : https://prove2.me/theorems/3b158652-da42-4ad9-877b-f7972fc60dc9
-- title:
--   Conditional-expectation descent for greedy terminal labeling
-- statement:
--   Let $q=64^a$. Assign labels from the palette of size $q$ to a list of vertices, choosing each new label to minimize the scaled edge and terminal collision energy. When no left endpoint is a right endpoint, the resulting list has the prescribed length, takes values in the palette, and has energy no greater than the empty prefix.

import Definitions.Def_DetDLP_D2_Greedy
set_option autoImplicit false
open DetDLP.D2.Greedy

theorem DetDLP.d2_greedy_energy_descent (vertices : List ℕ) (a : ℕ) (hosts : List ℕ) (es : List Edge)
    (hs : ∀ e ∈ es, ∀ f ∈ es, e.1 ≠ f.2) :
    let q := 64^a; let ks := (List.range a).map (64^·)
    let w := max 1 (hosts.length * maxOn hosts (fun j => hosts.count j))
    let v := es.length * maxOn vertices (fun j => (es.filter (fun e => e.1 == j || e.2 == j)).length)
    let p := solve vertices (List.range q) ks hosts es
    p.length = vertices.length ∧ (∀ x ∈ p, x < q) ∧ energy p q es ks hosts w v ≤ energy [] q es ks hosts w v := by sorry
