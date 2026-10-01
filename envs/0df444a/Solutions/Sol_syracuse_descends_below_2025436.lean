-- Prove2me | solution 1 for syracuse_descends_below_2025436
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T18:46:44.933377+00:00
-- url     : https://prove2.me/submissions/6088665c-5a9e-4924-89fe-51e1636a7dce

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_descends_below_1883432
import Theorems.Thm_syracuse_descends_range_1883435_1885435
import Theorems.Thm_syracuse_descends_range_1885435_1887435
import Theorems.Thm_syracuse_descends_range_1887435_1889435
import Theorems.Thm_syracuse_descends_range_1889435_1891435
import Theorems.Thm_syracuse_descends_range_1891435_1893435
import Theorems.Thm_syracuse_descends_range_1893435_1895435
import Theorems.Thm_syracuse_descends_range_1895435_1897435
import Theorems.Thm_syracuse_descends_range_1897435_1899435
import Theorems.Thm_syracuse_descends_range_1899435_1901435
import Theorems.Thm_syracuse_descends_range_1901435_1903435
import Theorems.Thm_syracuse_descends_range_1903435_1905435
import Theorems.Thm_syracuse_descends_range_1905435_1907435
import Theorems.Thm_syracuse_descends_range_1907435_1909435
import Theorems.Thm_syracuse_descends_range_1909435_1911435
import Theorems.Thm_syracuse_descends_range_1911435_1913435
import Theorems.Thm_syracuse_descends_range_1913435_1915435
import Theorems.Thm_syracuse_descends_range_1915435_1917435
import Theorems.Thm_syracuse_descends_range_1917435_1919435
import Theorems.Thm_syracuse_descends_range_1919435_1921435
import Theorems.Thm_syracuse_descends_range_1921435_1923435
import Theorems.Thm_syracuse_descends_range_1923435_1925435
import Theorems.Thm_syracuse_descends_range_1925435_1927435
import Theorems.Thm_syracuse_descends_range_1927435_1929435
import Theorems.Thm_syracuse_descends_range_1929435_1931435
import Theorems.Thm_syracuse_descends_range_1931435_1933435
import Theorems.Thm_syracuse_descends_range_1933435_1935435
import Theorems.Thm_syracuse_descends_range_1935435_1937435
import Theorems.Thm_syracuse_descends_range_1937435_1939435
import Theorems.Thm_syracuse_descends_range_1939435_1941435
import Theorems.Thm_syracuse_descends_range_1941435_1943435
import Theorems.Thm_syracuse_descends_range_1943435_1945435
import Theorems.Thm_syracuse_descends_range_1945435_1947435
import Theorems.Thm_syracuse_descends_range_1947435_1949435
import Theorems.Thm_syracuse_descends_range_1949435_1951435
import Theorems.Thm_syracuse_descends_range_1951435_1953435
import Theorems.Thm_syracuse_descends_range_1953435_1955435
import Theorems.Thm_syracuse_descends_range_1955435_1957435
import Theorems.Thm_syracuse_descends_range_1957435_1959435
import Theorems.Thm_syracuse_descends_range_1959435_1961435
import Theorems.Thm_syracuse_descends_range_1961435_1963435
import Theorems.Thm_syracuse_descends_range_1963435_1965435
import Theorems.Thm_syracuse_descends_range_1965435_1967435
import Theorems.Thm_syracuse_descends_range_1967435_1969435
import Theorems.Thm_syracuse_descends_range_1969435_1971435
import Theorems.Thm_syracuse_descends_range_1971435_1973435
import Theorems.Thm_syracuse_descends_range_1973435_1975435
import Theorems.Thm_syracuse_descends_range_1975435_1977435
import Theorems.Thm_syracuse_descends_range_1977435_1979435
import Theorems.Thm_syracuse_descends_range_1979435_1981435
import Theorems.Thm_syracuse_descends_range_1981435_1983435
import Theorems.Thm_syracuse_descends_range_1983435_1985435
import Theorems.Thm_syracuse_descends_range_1985435_1987435
import Theorems.Thm_syracuse_descends_range_1987435_1989435
import Theorems.Thm_syracuse_descends_range_1989435_1991435
import Theorems.Thm_syracuse_descends_range_1991435_1993435
import Theorems.Thm_syracuse_descends_range_1993435_1995435
import Theorems.Thm_syracuse_descends_range_1995435_1997435
import Theorems.Thm_syracuse_descends_range_1997435_1999435
import Theorems.Thm_syracuse_descends_range_1999435_2001435
import Theorems.Thm_syracuse_descends_range_2001435_2003435
import Theorems.Thm_syracuse_descends_range_2003435_2005435
import Theorems.Thm_syracuse_descends_range_2005435_2007435
import Theorems.Thm_syracuse_descends_range_2007435_2009435
import Theorems.Thm_syracuse_descends_range_2009435_2011435
import Theorems.Thm_syracuse_descends_range_2011435_2013435
import Theorems.Thm_syracuse_descends_range_2013435_2015435
import Theorems.Thm_syracuse_descends_range_2015435_2017435
import Theorems.Thm_syracuse_descends_range_2017435_2019435
import Theorems.Thm_syracuse_descends_range_2019435_2021435
import Theorems.Thm_syracuse_descends_range_2021435_2023435
import Theorems.Thm_syracuse_descends_range_2023435_2025435

set_option maxHeartbeats 1000000
theorem se (a : ℕ) {y z : ℕ} (h : 3 * y + 1 = 2 ^ a * z) (hz : Odd z) :
    syracuseStep y = z := by
  have hz0 : z ≠ 0 := by rintro rfl; simp [Nat.odd_iff] at hz
  have hfac : (3 * y + 1).factorization 2 = a := by
    rw [h, Nat.factorization_mul (by positivity) hz0]
    simp [Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by rwa [Nat.two_dvd_ne_zero, ← Nat.odd_iff])]
  show ordCompl[2] (3 * y + 1) = z
  rw [hfac, h, Nat.mul_div_cancel_left _ (by positivity)]
theorem solution (m : ℕ) (h1 : 1 < m) (hlt : m < 2025436) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  rcases Nat.lt_or_ge m 1883432 with hb | hb
  · exact syracuse_descends_below_1883432 m h1 hb hodd
  rcases Nat.lt_or_ge m 1883435 with hg | hg
  · obtain ⟨k, hk⟩ := hodd
    have hm : m = 1883433 := by omega
    have hstep : syracuseStep 1883433 = 1412575 :=
      se 2 (by norm_num) ⟨706287, by norm_num⟩
    rw [hm]
    exact ⟨1, by rw [Function.iterate_one, hstep]; norm_num⟩
  rcases Nat.lt_or_ge m 1885436 with hz0 | hz0
  · exact syracuse_descends_range_1883435_1885435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1887436 with hz1 | hz1
  · exact syracuse_descends_range_1885435_1887435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1889436 with hz2 | hz2
  · exact syracuse_descends_range_1887435_1889435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1891436 with hz3 | hz3
  · exact syracuse_descends_range_1889435_1891435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1893436 with hz4 | hz4
  · exact syracuse_descends_range_1891435_1893435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1895436 with hz5 | hz5
  · exact syracuse_descends_range_1893435_1895435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1897436 with hz6 | hz6
  · exact syracuse_descends_range_1895435_1897435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1899436 with hz7 | hz7
  · exact syracuse_descends_range_1897435_1899435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1901436 with hz8 | hz8
  · exact syracuse_descends_range_1899435_1901435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1903436 with hz9 | hz9
  · exact syracuse_descends_range_1901435_1903435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1905436 with hz10 | hz10
  · exact syracuse_descends_range_1903435_1905435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1907436 with hz11 | hz11
  · exact syracuse_descends_range_1905435_1907435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1909436 with hz12 | hz12
  · exact syracuse_descends_range_1907435_1909435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1911436 with hz13 | hz13
  · exact syracuse_descends_range_1909435_1911435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1913436 with hz14 | hz14
  · exact syracuse_descends_range_1911435_1913435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1915436 with hz15 | hz15
  · exact syracuse_descends_range_1913435_1915435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1917436 with hz16 | hz16
  · exact syracuse_descends_range_1915435_1917435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1919436 with hz17 | hz17
  · exact syracuse_descends_range_1917435_1919435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1921436 with hz18 | hz18
  · exact syracuse_descends_range_1919435_1921435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1923436 with hz19 | hz19
  · exact syracuse_descends_range_1921435_1923435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1925436 with hz20 | hz20
  · exact syracuse_descends_range_1923435_1925435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1927436 with hz21 | hz21
  · exact syracuse_descends_range_1925435_1927435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1929436 with hz22 | hz22
  · exact syracuse_descends_range_1927435_1929435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1931436 with hz23 | hz23
  · exact syracuse_descends_range_1929435_1931435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1933436 with hz24 | hz24
  · exact syracuse_descends_range_1931435_1933435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1935436 with hz25 | hz25
  · exact syracuse_descends_range_1933435_1935435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1937436 with hz26 | hz26
  · exact syracuse_descends_range_1935435_1937435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1939436 with hz27 | hz27
  · exact syracuse_descends_range_1937435_1939435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1941436 with hz28 | hz28
  · exact syracuse_descends_range_1939435_1941435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1943436 with hz29 | hz29
  · exact syracuse_descends_range_1941435_1943435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1945436 with hz30 | hz30
  · exact syracuse_descends_range_1943435_1945435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1947436 with hz31 | hz31
  · exact syracuse_descends_range_1945435_1947435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1949436 with hz32 | hz32
  · exact syracuse_descends_range_1947435_1949435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1951436 with hz33 | hz33
  · exact syracuse_descends_range_1949435_1951435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1953436 with hz34 | hz34
  · exact syracuse_descends_range_1951435_1953435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1955436 with hz35 | hz35
  · exact syracuse_descends_range_1953435_1955435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1957436 with hz36 | hz36
  · exact syracuse_descends_range_1955435_1957435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1959436 with hz37 | hz37
  · exact syracuse_descends_range_1957435_1959435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1961436 with hz38 | hz38
  · exact syracuse_descends_range_1959435_1961435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1963436 with hz39 | hz39
  · exact syracuse_descends_range_1961435_1963435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1965436 with hz40 | hz40
  · exact syracuse_descends_range_1963435_1965435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1967436 with hz41 | hz41
  · exact syracuse_descends_range_1965435_1967435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1969436 with hz42 | hz42
  · exact syracuse_descends_range_1967435_1969435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1971436 with hz43 | hz43
  · exact syracuse_descends_range_1969435_1971435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1973436 with hz44 | hz44
  · exact syracuse_descends_range_1971435_1973435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1975436 with hz45 | hz45
  · exact syracuse_descends_range_1973435_1975435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1977436 with hz46 | hz46
  · exact syracuse_descends_range_1975435_1977435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1979436 with hz47 | hz47
  · exact syracuse_descends_range_1977435_1979435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1981436 with hz48 | hz48
  · exact syracuse_descends_range_1979435_1981435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1983436 with hz49 | hz49
  · exact syracuse_descends_range_1981435_1983435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1985436 with hz50 | hz50
  · exact syracuse_descends_range_1983435_1985435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1987436 with hz51 | hz51
  · exact syracuse_descends_range_1985435_1987435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1989436 with hz52 | hz52
  · exact syracuse_descends_range_1987435_1989435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1991436 with hz53 | hz53
  · exact syracuse_descends_range_1989435_1991435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1993436 with hz54 | hz54
  · exact syracuse_descends_range_1991435_1993435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1995436 with hz55 | hz55
  · exact syracuse_descends_range_1993435_1995435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1997436 with hz56 | hz56
  · exact syracuse_descends_range_1995435_1997435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 1999436 with hz57 | hz57
  · exact syracuse_descends_range_1997435_1999435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2001436 with hz58 | hz58
  · exact syracuse_descends_range_1999435_2001435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2003436 with hz59 | hz59
  · exact syracuse_descends_range_2001435_2003435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2005436 with hz60 | hz60
  · exact syracuse_descends_range_2003435_2005435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2007436 with hz61 | hz61
  · exact syracuse_descends_range_2005435_2007435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2009436 with hz62 | hz62
  · exact syracuse_descends_range_2007435_2009435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2011436 with hz63 | hz63
  · exact syracuse_descends_range_2009435_2011435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2013436 with hz64 | hz64
  · exact syracuse_descends_range_2011435_2013435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2015436 with hz65 | hz65
  · exact syracuse_descends_range_2013435_2015435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2017436 with hz66 | hz66
  · exact syracuse_descends_range_2015435_2017435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2019436 with hz67 | hz67
  · exact syracuse_descends_range_2017435_2019435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2021436 with hz68 | hz68
  · exact syracuse_descends_range_2019435_2021435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2023436 with hz69 | hz69
  · exact syracuse_descends_range_2021435_2023435 m (by omega) (by omega) hodd
  exact syracuse_descends_range_2023435_2025435 m (by omega) (by omega) hodd
