-- Prove2me | solution 1 for isPreconnected_iInter_of_antitone_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-15T21:45:55.907425+00:00
-- url     : https://prove2.me/submissions/17eb2d52-d52d-40c8-8d18-fae1801f84b5

import Mathlib

open Set Topology

theorem solution
    {α : Type*} [TopologicalSpace α] [T2Space α] {s : ℕ → Set α}
    (hanti : Antitone s) (hcomp : ∀ n, IsCompact (s n))
    (hconn : ∀ n, IsPreconnected (s n)) :
    IsPreconnected (⋂ n, s n) := by
  have hKcl : IsClosed (⋂ n, s n) := isClosed_iInter fun n => (hcomp n).isClosed
  have hKcomp : IsCompact (⋂ n, s n) :=
    (hcomp 0).of_isClosed_subset hKcl (iInter_subset s 0)
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed hKcl]
  intro u v hu hv hsub hdisj
  by_contra hcon
  push Not at hcon
  obtain ⟨hnu, hnv⟩ := hcon
  have hAne : ((⋂ n, s n) ∩ u).Nonempty := by
    obtain ⟨x, hxK, hxv⟩ := not_subset.mp hnv
    rcases hsub hxK with h | h
    · exact ⟨x, hxK, h⟩
    · exact absurd h hxv
  have hBne : ((⋂ n, s n) ∩ v).Nonempty := by
    obtain ⟨x, hxK, hxu⟩ := not_subset.mp hnu
    rcases hsub hxK with h | h
    · exact absurd h hxu
    · exact ⟨x, hxK, h⟩
  have hABd : Disjoint ((⋂ n, s n) ∩ u) ((⋂ n, s n) ∩ v) :=
    hdisj.mono inter_subset_right inter_subset_right
  obtain ⟨U, V, hUo, hVo, hAU, hBV, hUV⟩ :=
    SeparatedNhds.of_isCompact_isCompact (hKcomp.inter_right hu) (hKcomp.inter_right hv) hABd
  have hKUV : (⋂ n, s n) ⊆ U ∪ V := by
    intro x hx
    rcases hsub hx with h | h
    · exact Or.inl (hAU ⟨hx, h⟩)
    · exact Or.inr (hBV ⟨hx, h⟩)
  have hex : ∃ n, s n ⊆ U ∪ V := by
    by_contra hno
    push Not at hno
    have hne : ∀ n, (s n \ (U ∪ V)).Nonempty := by
      intro n
      obtain ⟨x, hx1, hx2⟩ := not_subset.mp (hno n)
      exact ⟨x, hx1, hx2⟩
    have htc : ∀ n, IsCompact (s n \ (U ∪ V)) := fun n => (hcomp n).diff (hUo.union hVo)
    have hanti' : Antitone (fun n => s n \ (U ∪ V)) := fun a b hab =>
      Set.sdiff_subset_sdiff_left (hanti hab)
    have hdir : Directed (· ⊇ ·) (fun n => s n \ (U ∪ V)) := hanti'.directed_ge
    obtain ⟨x, hx⟩ :=
      IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
        (fun n => s n \ (U ∪ V)) hdir hne htc (fun n => (htc n).isClosed)
    simp only [mem_iInter, Set.mem_sdiff] at hx
    exact (hx 0).2 (hKUV (mem_iInter.2 fun n => (hx n).1))
  obtain ⟨n, hn⟩ := hex
  have hKsn : (⋂ m, s m) ⊆ s n := iInter_subset s n
  obtain ⟨y, -, hyU, hyV⟩ :=
    hconn n U V hUo hVo hn
      (hAne.mono (fun x hx => ⟨hKsn hx.1, hAU hx⟩))
      (hBne.mono (fun x hx => ⟨hKsn hx.1, hBV hx⟩))
  exact (hUV.le_bot ⟨hyU, hyV⟩ : y ∈ (⊥ : Set α))
