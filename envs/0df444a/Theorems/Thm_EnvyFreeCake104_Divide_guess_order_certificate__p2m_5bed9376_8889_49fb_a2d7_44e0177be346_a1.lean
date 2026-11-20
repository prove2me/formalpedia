-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_guess_order_certificate__p2m_5bed9376_8889_49fb_a2d7_44e0177be346_a1
-- name    : EnvyFreeCake104.Divide.guess_order_certificate__p2m_5bed9376_8889_49fb_a2d7_44e0177be346_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-19T09:12:30.362073+00:00
-- url     : https://prove2.me/theorems/17e4bd5c-6333-4134-a2ab-4b9962e50e4d
-- title:
--   Two enumerations give a matching and an earlier-agent rank
-- statement:
--   A guessed pair of orderings determines a bijection of the participating agents and natural-number ranks. Every participating agent occurs paired with its image, and all agents preceding that pair have strictly smaller ranks.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.10, Lemma 6 (restated p.13)

import Definitions.Def_EnvyFreeCake104_Divide_Protocols

open EnvyFreeCake104.Divide

theorem EnvyFreeCake104.Divide.guess_order_certificate__p2m_5bed9376_8889_49fb_a2d7_44e0177be346_a1
    {ι : Type} [DecidableEq ι] (N : Finset ι)
    (g : List ι × List ι) (hg : g ∈ guesses N) :
    g.1.Nodup ∧
    (∀ p ∈ g.1.zip g.2, p.1 ∈ N ∧ p.2 ∈ N) ∧
    ∃ (π : ι → ι) (rank : ι → ℕ),
      Set.BijOn π (N : Set ι) (N : Set ι) ∧
      ∀ i ∈ N, ∃ (before after : List (ι × ι)),
        g.1.zip g.2 = before ++ (i, π i) :: after ∧
        ∀ j ∈ before.map Prod.fst, j ∈ N ∧ rank j < rank i := by sorry
